Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_UNIONS_NONZERO_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import FINITE_UNIONS_spec.
Require Import IN_INSERT_spec.
Require Import IN_INTER_spec.
Require Import IN_UNIONS_spec.
Require Import NSUM_CLAUSES_spec.
Require Import NSUM_UNION_NONZERO_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm129_spec.
Require Import thm137_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
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
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm3322101_spec.
Require Import thm3322164_spec.
Require Import thm3324017_spec.
Require Import thm3325374_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem7018614 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7018615 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem7018616 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem7018615 t1) (@lem7018614 t1)). Qed.
Lemma lem7018617 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem7018616 t1 t2). Qed.
Lemma lem7018618 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem7018619 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem7018618 t1 t2) (@lem7018617 t1 t2)). Qed.
Lemma lem7018620 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem7018619 t1 t2 t3). Qed.
Lemma lem7018621 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem7018622 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem7018621 t1 t2 t3) (@lem7018620 t1 t2 t3)). Qed.
Lemma lem7018623 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem7018622 t1 t2 t3)). Qed.
Lemma lem7018624 {_129614 : Type'} (h1 : term7 _129614) : term7 _129614.
Proof. exact (h1). Qed.
Lemma lem7018625 {_129614 : Type'} (f : _129614 -> nat) (h1 : term7 _129614) : term8 _129614 f.
Proof. exact (@lem7018624 _129614 h1 f). Qed.
Lemma lem7018626 {_129614 : Type'} (f : _129614 -> nat) : (term8 _129614 f) = (term9 _129614 f).
Proof. exact (eq_refl (term8 _129614 f)). Qed.
Lemma lem7018627 {_129614 : Type'} (f : _129614 -> nat) (h1 : term7 _129614) : term9 _129614 f.
Proof. exact (EQ_MP (@lem7018626 _129614 f) (@lem7018625 _129614 f h1)). Qed.
Lemma lem7018628 {_129614 : Type'} (f : _129614 -> nat) (s : _129614 -> Prop) (h1 : term7 _129614) : term10 _129614 f s.
Proof. exact (@lem7018627 _129614 f h1 s). Qed.
Lemma lem7018629 {_129614 : Type'} (s : _129614 -> Prop) (f : _129614 -> nat) : (term10 _129614 f s) = (term11 _129614 s f).
Proof. exact (eq_refl (term10 _129614 f s)). Qed.
Lemma lem7018630 {_129614 : Type'} (s : _129614 -> Prop) (f : _129614 -> nat) (h1 : term7 _129614) : term11 _129614 s f.
Proof. exact (EQ_MP (@lem7018629 _129614 s f) (@lem7018628 _129614 f s h1)). Qed.
Lemma lem7018631 {_129614 : Type'} (s : _129614 -> Prop) (f : _129614 -> nat) (t : _129614 -> Prop) (h1 : term7 _129614) : term12 _129614 s f t.
Proof. exact (@lem7018630 _129614 s f h1 t). Qed.
Lemma lem7018632 {_129614 : Type'} (s : _129614 -> Prop) (t : _129614 -> Prop) (f : _129614 -> nat) : (term12 _129614 s f t) = (term13 _129614 s t f).
Proof. exact (eq_refl (term12 _129614 s f t)). Qed.
Lemma lem7018633 {_129614 : Type'} (s : _129614 -> Prop) (t : _129614 -> Prop) (f : _129614 -> nat) (h1 : term7 _129614) : term13 _129614 s t f.
Proof. exact (EQ_MP (@lem7018632 _129614 s t f) (@lem7018631 _129614 s f t h1)). Qed.
Lemma lem7018634 {_129614 : Type'} (s : _129614 -> Prop) (t : _129614 -> Prop) (f : _129614 -> nat) (h1 : term14 _129614 s t f) : term14 _129614 s t f.
Proof. exact (h1). Qed.
Lemma lem7018635 {_129614 : Type'} (s : _129614 -> Prop) (t : _129614 -> Prop) (f : _129614 -> nat) (h1 : term7 _129614) (h2 : term14 _129614 s t f) : (term15 _129614 s t f) = (term16 _129614 s t f).
Proof. exact (@lem7018633 _129614 s t f h1 (@lem7018634 _129614 s t f h2)). Qed.
Lemma lem7018636 {_129614 : Type'} (s : _129614 -> Prop) (t : _129614 -> Prop) (f : _129614 -> nat) (h1 : term14 _129614 s t f) : term17 _129614 s t f.
Proof. exact (fun h0 : term7 _129614 => @lem7018635 _129614 s t f h0 h1). Qed.
Lemma lem7018637 {_129614 : Type'} (h1 : term7 _129614) : term7 _129614.
Proof. exact (h1). Qed.
Lemma lem7018638 {_129614 : Type'} (s : _129614 -> Prop) (t : _129614 -> Prop) (f : _129614 -> nat) (h1 : term7 _129614) (h2 : term14 _129614 s t f) : (term15 _129614 s t f) = (term16 _129614 s t f).
Proof. exact (@lem7018636 _129614 s t f h2 (@lem7018637 _129614 h1)). Qed.
Lemma lem7018639 {_129614 : Type'} (s : _129614 -> Prop) (t : _129614 -> Prop) (f : _129614 -> nat) (h1 : term7 _129614) : term13 _129614 s t f.
Proof. exact (fun h0 : term14 _129614 s t f => @lem7018638 _129614 s t f h1 h0). Qed.
Lemma lem7018640 {_129614 : Type'} (s : _129614 -> Prop) (t : _129614 -> Prop) (h1 : term7 _129614) : term18 _129614 s t.
Proof. exact (fun f : _129614 -> nat => @lem7018639 _129614 s t f h1). Qed.
Lemma lem7018641 {_129614 : Type'} (s : _129614 -> Prop) (h1 : term7 _129614) : term19 _129614 s.
Proof. exact (fun t : _129614 -> Prop => @lem7018640 _129614 s t h1). Qed.
Lemma lem7018642 {_129614 : Type'} (h1 : term7 _129614) : term20 _129614.
Proof. exact (fun s : _129614 -> Prop => @lem7018641 _129614 s h1). Qed.
Lemma lem7018643 {_129614 : Type'} : term21 _129614.
Proof. exact (fun h0 : term7 _129614 => @lem7018642 _129614 h0). Qed.
Lemma lem7018644 {_129614 : Type'} : term20 _129614.
Proof. exact (@lem7018643 _129614 (@lem7018613 _129614)). Qed.
Lemma lem7018645 {_129614 : Type'} (s : _129614 -> Prop) : term22 _129614 s.
Proof. exact (@lem7018644 _129614 s). Qed.
Lemma lem7018646 {_129614 : Type'} (s : _129614 -> Prop) : (term22 _129614 s) = (term19 _129614 s).
Proof. exact (eq_refl (term22 _129614 s)). Qed.
Lemma lem7018647 {_129614 : Type'} (s : _129614 -> Prop) : term19 _129614 s.
Proof. exact (EQ_MP (@lem7018646 _129614 s) (@lem7018645 _129614 s)). Qed.
Lemma lem7018648 {_129614 : Type'} (s : _129614 -> Prop) (t : _129614 -> Prop) : term23 _129614 s t.
Proof. exact (@lem7018647 _129614 s t). Qed.
Lemma lem7018649 {_129614 : Type'} (s : _129614 -> Prop) (t : _129614 -> Prop) : (term23 _129614 s t) = (term18 _129614 s t).
Proof. exact (eq_refl (term23 _129614 s t)). Qed.
Lemma lem7018650 {_129614 : Type'} (s : _129614 -> Prop) (t : _129614 -> Prop) : term18 _129614 s t.
Proof. exact (EQ_MP (@lem7018649 _129614 s t) (@lem7018648 _129614 s t)). Qed.
Lemma lem7018651 {_129614 : Type'} (s : _129614 -> Prop) (t : _129614 -> Prop) (f : _129614 -> nat) : term24 _129614 s t f.
Proof. exact (@lem7018650 _129614 s t f). Qed.
Lemma lem7018652 {_129614 : Type'} (s : _129614 -> Prop) (t : _129614 -> Prop) (f : _129614 -> nat) : (term24 _129614 s t f) = (term13 _129614 s t f).
Proof. exact (eq_refl (term24 _129614 s t f)). Qed.
Lemma lem7018654 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7018655 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem7018656 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem7018655 t1) (@lem7018654 t1)). Qed.
Lemma lem7018657 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem7018656 t1 t2). Qed.
Lemma lem7018658 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem7018659 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem7018658 t1 t2) (@lem7018657 t1 t2)). Qed.
Lemma lem7018660 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem7018659 t1 t2 t3). Qed.
Lemma lem7018661 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem7018662 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem7018661 t1 t2 t3) (@lem7018660 t1 t2 t3)). Qed.
Lemma lem7018663 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem7018662 t1 t2 t3)). Qed.
Lemma lem7018664 {A : Type'} (x : A) : term25 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem7018665 {A : Type'} (x : A) : (term25 A x) = (term26 A x).
Proof. exact (eq_refl (term25 A x)). Qed.
Lemma lem7018666 {A : Type'} (x : A) : term26 A x.
Proof. exact (EQ_MP (@lem7018665 A x) (@lem7018664 A x)). Qed.
Lemma lem7018667 {A : Type'} (x : A) (y : A) : term27 A x y.
Proof. exact (@lem7018666 A x y). Qed.
Lemma lem7018668 {A : Type'} (y : A) (x : A) : (term27 A x y) = (term28 A y x).
Proof. exact (eq_refl (term27 A x y)). Qed.
Lemma lem7018669 {A : Type'} (y : A) (x : A) : term28 A y x.
Proof. exact (EQ_MP (@lem7018668 A y x) (@lem7018667 A x y)). Qed.
Lemma lem7018670 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term29 A y x s.
Proof. exact (@lem7018669 A y x s). Qed.
Lemma lem7018671 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term29 A y x s) = ((term30 A x y s) = (term31 A y x s)).
Proof. exact (eq_refl (term29 A y x s)). Qed.
Lemma lem7018685 {_126486 : Type'} : term32 _126486.
Proof. exact (proj1 (@lem6924916 _126486 Prop)). Qed.
Lemma lem7018686 {_126486 : Type'} (f : _126486 -> nat) : term33 _126486 f.
Proof. exact (@lem7018685 _126486 f). Qed.
Lemma lem7018687 {_126486 : Type'} (f : _126486 -> nat) : (term33 _126486 f) = ((@nsum _126486 (@EMPTY _126486) f) = (NUMERAL 0)).
Proof. exact (eq_refl (term33 _126486 f)). Qed.
Lemma lem7018689 {A : Type'} (h1 : term34 A) : term34 A.
Proof. exact (h1). Qed.
Lemma lem7018690 {A : Type'} (P : type686 A) (h1 : term34 A) : term35 A P.
Proof. exact (@lem7018689 A h1 P). Qed.
Lemma lem7018691 {A : Type'} (P : type686 A) : (term35 A P) = (term36 A P).
Proof. exact (eq_refl (term35 A P)). Qed.
Lemma lem7018692 {A : Type'} (P : type686 A) (h1 : term34 A) : term36 A P.
Proof. exact (EQ_MP (@lem7018691 A P) (@lem7018690 A P h1)). Qed.
Lemma lem7018693 {A : Type'} (P : type686 A) (h1 : term37 A P) : term37 A P.
Proof. exact (h1). Qed.
Lemma lem7018694 {A : Type'} (P : type686 A) (h1 : term34 A) (h2 : term37 A P) : term38 A P.
Proof. exact (@lem7018692 A P h1 (@lem7018693 A P h2)). Qed.
Lemma lem7018695 {A : Type'} (P : type686 A) (h1 : term37 A P) : term39 A P.
Proof. exact (fun h0 : term34 A => @lem7018694 A P h0 h1). Qed.
Lemma lem7018696 {A : Type'} (h1 : term34 A) : term34 A.
Proof. exact (h1). Qed.
Lemma lem7018697 {A : Type'} (P : type686 A) (h1 : term34 A) (h2 : term37 A P) : term38 A P.
Proof. exact (@lem7018695 A P h2 (@lem7018696 A h1)). Qed.
Lemma lem7018698 {A : Type'} (P : type686 A) (h1 : term34 A) : term36 A P.
Proof. exact (fun h0 : term37 A P => @lem7018697 A P h1 h0). Qed.
Lemma lem7018699 {A : Type'} (h1 : term34 A) : term34 A.
Proof. exact (fun P : type686 A => @lem7018698 A P h1). Qed.
Lemma lem7018700 {A : Type'} : term40 A.
Proof. exact (fun h0 : term34 A => @lem7018699 A h0). Qed.
Lemma lem7018701 {A : Type'} : term34 A.
Proof. exact (@lem7018700 A (@lem3558722 A)). Qed.
Lemma lem7018702 {A : Type'} (P : type686 A) : term35 A P.
Proof. exact (@lem7018701 A P). Qed.
Lemma lem7018703 {A : Type'} (P : type686 A) : (term35 A P) = (term36 A P).
Proof. exact (eq_refl (term35 A P)). Qed.
Lemma lem7018710 (p : Prop) (q : Prop) (r : Prop) : (term41 p q r) = (term42 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7018711 {A : Type'} (s : type686 A) (f : A -> nat) : (term43 A s f) = (term44 A s f).
Proof. exact (@lem7018710 (@FINITE (A -> Prop) s) (term45 A s f) ((term46 A s f) = (term47 A s f))). Qed.
Lemma lem7018712 {A : Type'} (f : A -> nat) : (term48 A f) = (term49 A f).
Proof. exact (fun_ext (fun s : type686 A => @lem7018711 A s f)). Qed.
Lemma lem7018713 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem7018714 {A : Type'} (f : A -> nat) : (term50 A f) = (term51 A f).
Proof. exact (MK_COMB (@lem7018713 A) (@lem7018712 A f)). Qed.
Lemma lem7018715 {A : Type'} (f : A -> nat) : (term51 A f) = (term50 A f).
Proof. exact (SYM (@lem7018714 A f)). Qed.
Lemma lem7018717 {A : Type'} (P : type686 A) : term36 A P.
Proof. exact (EQ_MP (@lem7018703 A P) (@lem7018702 A P)). Qed.
Lemma lem7018718 {A : Type'} (P : type180 A) : term52 A P.
Proof. exact (@lem7018717 (A -> Prop) P). Qed.
Lemma lem7018719 {A : Type'} (f : A -> nat) : term53 A f.
Proof. exact (@lem7018718 A (term54 A f)). Qed.
Lemma lem7018720 {A : Type'} (f : A -> nat) : (term55 A f) = (term56 A f).
Proof. exact (eq_refl (term55 A f)). Qed.
Lemma lem7018721 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7018722 {A : Type'} (f : A -> nat) : (term57 A f) = (term58 A f).
Proof. exact (MK_COMB (@lem7018721) (@lem7018720 A f)). Qed.
Lemma lem7018723 {A : Type'} (s : type686 A) (f : A -> nat) : (term59 A f s) = (term60 A s f).
Proof. exact (eq_refl (term59 A f s)). Qed.
Lemma lem7018724 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7018725 {A : Type'} (s : type686 A) (f : A -> nat) : (term61 A f s) = (term62 A s f).
Proof. exact (MK_COMB (@lem7018724) (@lem7018723 A s f)). Qed.
Lemma lem7018726 {A : Type'} (x : A -> Prop) (s : type686 A) : (term63 A x s) = (term63 A x s).
Proof. exact (eq_refl (term63 A x s)). Qed.
Lemma lem7018727 {A : Type'} (f : A -> nat) (x : A -> Prop) (s : type686 A) : (term64 A f x s) = (term65 A f x s).
Proof. exact (MK_COMB (@lem7018725 A s f) (@lem7018726 A x s)). Qed.
Lemma lem7018728 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7018729 {A : Type'} (f : A -> nat) (x : A -> Prop) (s : type686 A) : (term66 A f x s) = (term67 A f x s).
Proof. exact (MK_COMB (@lem7018728) (@lem7018727 A f x s)). Qed.
Lemma lem7018730 {A : Type'} (x : A -> Prop) (s : type686 A) (f : A -> nat) : (term68 A f x s) = (term69 A x s f).
Proof. exact (eq_refl (term68 A f x s)). Qed.
Lemma lem7018731 {A : Type'} (x : A -> Prop) (s : type686 A) (f : A -> nat) : (term70 A f x s) = (term71 A x s f).
Proof. exact (MK_COMB (@lem7018729 A f x s) (@lem7018730 A x s f)). Qed.
Lemma lem7018732 {A : Type'} (x : A -> Prop) (f : A -> nat) : (term72 A f x) = (term73 A x f).
Proof. exact (fun_ext (fun s : type686 A => @lem7018731 A x s f)). Qed.
Lemma lem7018733 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem7018734 {A : Type'} (x : A -> Prop) (f : A -> nat) : (term74 A f x) = (term75 A x f).
Proof. exact (MK_COMB (@lem7018733 A) (@lem7018732 A x f)). Qed.
Lemma lem7018735 {A : Type'} (f : A -> nat) : (term76 A f) = (term77 A f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem7018734 A x f)). Qed.
Lemma lem7018736 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7018737 {A : Type'} (f : A -> nat) : (term78 A f) = (term79 A f).
Proof. exact (MK_COMB (@lem7018736 A) (@lem7018735 A f)). Qed.
Lemma lem7018738 {A : Type'} (f : A -> nat) : (term80 A f) = (term81 A f).
Proof. exact (MK_COMB (@lem7018722 A f) (@lem7018737 A f)). Qed.
Lemma lem7018739 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7018740 {A : Type'} (f : A -> nat) : (term82 A f) = (term83 A f).
Proof. exact (MK_COMB (@lem7018739) (@lem7018738 A f)). Qed.
Lemma lem7018741 {A : Type'} (s : type686 A) (f : A -> nat) : (term59 A f s) = (term60 A s f).
Proof. exact (eq_refl (term59 A f s)). Qed.
Lemma lem7018742 {A : Type'} (s : type686 A) : (term84 A s) = (term84 A s).
Proof. exact (eq_refl (term84 A s)). Qed.
Lemma lem7018743 {A : Type'} (s : type686 A) (f : A -> nat) : (term85 A f s) = (term44 A s f).
Proof. exact (MK_COMB (@lem7018742 A s) (@lem7018741 A s f)). Qed.
Lemma lem7018744 {A : Type'} (f : A -> nat) : (term86 A f) = (term49 A f).
Proof. exact (fun_ext (fun s : type686 A => @lem7018743 A s f)). Qed.
Lemma lem7018745 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem7018746 {A : Type'} (f : A -> nat) : (term87 A f) = (term51 A f).
Proof. exact (MK_COMB (@lem7018745 A) (@lem7018744 A f)). Qed.
Lemma lem7018747 {A : Type'} (f : A -> nat) : (term53 A f) = (term88 A f).
Proof. exact (MK_COMB (@lem7018740 A f) (@lem7018746 A f)). Qed.
Lemma lem7018748 {A : Type'} (f : A -> nat) : term88 A f.
Proof. exact (EQ_MP (@lem7018747 A f) (@lem7018719 A f)). Qed.
Lemma lem7018790 {_86801 : Type'} : (@UNIONS _86801 (@EMPTY (_86801 -> Prop))) = (@EMPTY _86801).
Proof. exact (EQ_MP (@lem3322101 _86801) (@lem3322164 _86801)). Qed.
Lemma lem7018791 {A : Type'} : (@UNIONS A (@EMPTY (A -> Prop))) = (@EMPTY A).
Proof. exact (@lem7018790 A). Qed.
Lemma lem7018792 {A : Type'} : (@nsum A) = (@nsum A).
Proof. exact (eq_refl (@nsum A)). Qed.
Lemma lem7018793 {A : Type'} : (term89 A) = (@nsum A (@EMPTY A)).
Proof. exact (MK_COMB (@lem7018792 A) (@lem7018791 A)). Qed.
Lemma lem7018794 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7018795 {A : Type'} (f : A -> nat) : (term90 A f) = (@nsum A (@EMPTY A) f).
Proof. exact (MK_COMB (@lem7018793 A) (@lem7018794 A f)). Qed.
Lemma lem7018797 {_126486 : Type'} (f : _126486 -> nat) : (@nsum _126486 (@EMPTY _126486) f) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem7018687 _126486 f) (@lem7018686 _126486 f)). Qed.
Lemma lem7018798 {A : Type'} (f : A -> nat) : (@nsum A (@EMPTY A) f) = (NUMERAL 0).
Proof. exact (@lem7018797 A f). Qed.
Lemma lem7018799 {A : Type'} (f : A -> nat) : (term90 A f) = (NUMERAL 0).
Proof. exact (TRANS (@lem7018795 A f) (@lem7018798 A f)). Qed.
Lemma lem7018800 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7018801 {A : Type'} (f : A -> nat) : (term91 A f) = term92.
Proof. exact (MK_COMB (@lem7018800) (@lem7018799 A f)). Qed.
Lemma lem7018803 {_126486 : Type'} (f : _126486 -> nat) : (@nsum _126486 (@EMPTY _126486) f) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem7018687 _126486 f) (@lem7018686 _126486 f)). Qed.
Lemma lem7018804 {A : Type'} (f : type687 A) : (@nsum (A -> Prop) (@EMPTY (A -> Prop)) f) = (NUMERAL 0).
Proof. exact (@lem7018803 (A -> Prop) f). Qed.
Lemma lem7018805 {A : Type'} (f : A -> nat) : (term93 A f) = (NUMERAL 0).
Proof. exact (@lem7018804 A (term94 A f)). Qed.
Lemma lem7018806 {A : Type'} (f : A -> nat) : ((term90 A f) = (term93 A f)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem7018801 A f) (@lem7018805 A f)). Qed.
Lemma lem7018808 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7018809 (x : nat) : (x = x) = True.
Proof. exact (@lem7018808 nat x). Qed.
Lemma lem7018810 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem7018809 (NUMERAL 0)). Qed.
Lemma lem7018811 {A : Type'} (f : A -> nat) : ((term90 A f) = (term93 A f)) = True.
Proof. exact (TRANS (@lem7018806 A f) (@lem7018810)). Qed.
Lemma lem7018812 {A : Type'} (f : A -> nat) : (term95 A f) = (term95 A f).
Proof. exact (eq_refl (term95 A f)). Qed.
Lemma lem7018813 {A : Type'} (f : A -> nat) : (term56 A f) = (term96 A f).
Proof. exact (MK_COMB (@lem7018812 A f) (@lem7018811 A f)). Qed.
Lemma lem7018815 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7018816 {A : Type'} (f : A -> nat) : (term96 A f) = True.
Proof. exact (@lem7018815 (term97 A f)). Qed.
Lemma lem7018817 {A : Type'} (f : A -> nat) : (term56 A f) = True.
Proof. exact (TRANS (@lem7018813 A f) (@lem7018816 A f)). Qed.
Lemma lem7018818 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7018819 {A : Type'} (f : A -> nat) : (term58 A f) = (and True).
Proof. exact (MK_COMB (@lem7018818) (@lem7018817 A f)). Qed.
Lemma lem7018883 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term30 A x y s) = (term31 A y x s).
Proof. exact (EQ_MP (@lem7018671 A y x s) (@lem7018670 A y x s)). Qed.
Lemma lem7018884 {A : Type'} (y : A -> Prop) (x : A -> Prop) (s : type686 A) : (term98 A x y s) = (term99 A y x s).
Proof. exact (@lem7018883 (A -> Prop) y x s). Qed.
Lemma lem7018885 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : type686 A) : (term98 A t x s) = (term99 A x t s).
Proof. exact (@lem7018884 A x t s). Qed.
Lemma lem7018890 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7018891 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : type686 A) : (term100 A t x s) = (term101 A x t s).
Proof. exact (MK_COMB (@lem7018890) (@lem7018885 A x t s)). Qed.
Lemma lem7018892 {A : Type'} (t : A -> Prop) : (@FINITE A t) = (@FINITE A t).
Proof. exact (eq_refl (@FINITE A t)). Qed.
Lemma lem7018893 {A : Type'} (x : A -> Prop) (s : type686 A) (t : A -> Prop) : (term102 A x s t) = (term103 A x s t).
Proof. exact (MK_COMB (@lem7018891 A x t s) (@lem7018892 A t)). Qed.
Lemma lem7018896 {A : Type'} (x : A -> Prop) (s : type686 A) : (term104 A x s) = (term105 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7018893 A x s t)). Qed.
Lemma lem7018897 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7018898 {A : Type'} (x : A -> Prop) (s : type686 A) : (term106 A x s) = (term107 A x s).
Proof. exact (MK_COMB (@lem7018897 A) (@lem7018896 A x s)). Qed.
Lemma lem7018903 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7018904 {A : Type'} (x : A -> Prop) (s : type686 A) : (term108 A x s) = (term109 A x s).
Proof. exact (MK_COMB (@lem7018903) (@lem7018898 A x s)). Qed.
Lemma lem7018922 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term30 A x y s) = (term31 A y x s).
Proof. exact (EQ_MP (@lem7018671 A y x s) (@lem7018670 A y x s)). Qed.
Lemma lem7018923 {A : Type'} (y : A -> Prop) (x : A -> Prop) (s : type686 A) : (term98 A x y s) = (term99 A y x s).
Proof. exact (@lem7018922 (A -> Prop) y x s). Qed.
Lemma lem7018924 {A : Type'} (x : A -> Prop) (t1 : A -> Prop) (s : type686 A) : (term98 A t1 x s) = (term99 A x t1 s).
Proof. exact (@lem7018923 A x t1 s). Qed.
Lemma lem7018929 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7018930 {A : Type'} (x : A -> Prop) (t1 : A -> Prop) (s : type686 A) : (term110 A t1 x s) = (term111 A x t1 s).
Proof. exact (MK_COMB (@lem7018929) (@lem7018924 A x t1 s)). Qed.
Lemma lem7018934 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term30 A x y s) = (term31 A y x s).
Proof. exact (EQ_MP (@lem7018671 A y x s) (@lem7018670 A y x s)). Qed.
Lemma lem7018935 {A : Type'} (y : A -> Prop) (x : A -> Prop) (s : type686 A) : (term98 A x y s) = (term99 A y x s).
Proof. exact (@lem7018934 (A -> Prop) y x s). Qed.
Lemma lem7018936 {A : Type'} (x : A -> Prop) (t2 : A -> Prop) (s : type686 A) : (term98 A t2 x s) = (term99 A x t2 s).
Proof. exact (@lem7018935 A x t2 s). Qed.
Lemma lem7018941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7018942 {A : Type'} (x : A -> Prop) (t2 : A -> Prop) (s : type686 A) : (term110 A t2 x s) = (term111 A x t2 s).
Proof. exact (MK_COMB (@lem7018941) (@lem7018936 A x t2 s)). Qed.
Lemma lem7018949 {A : Type'} (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term112 A t1 x t2) = (term112 A t1 x t2).
Proof. exact (eq_refl (term112 A t1 x t2)). Qed.
Lemma lem7018950 {A : Type'} (x : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x' : A) (t2 : A -> Prop) : (term113 A x s t1 x' t2) = (term114 A x s t1 x' t2).
Proof. exact (MK_COMB (@lem7018942 A x t2 s) (@lem7018949 A t1 x' t2)). Qed.
Lemma lem7018953 {A : Type'} (x : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x' : A) (t2 : A -> Prop) : (term115 A x s t1 x' t2) = (term116 A x s t1 x' t2).
Proof. exact (MK_COMB (@lem7018930 A x t1 s) (@lem7018950 A x s t1 x' t2)). Qed.
Lemma lem7018956 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7018957 {A : Type'} (x : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x' : A) (t2 : A -> Prop) : (term117 A x s t1 x' t2) = (term118 A x s t1 x' t2).
Proof. exact (MK_COMB (@lem7018956) (@lem7018953 A x s t1 x' t2)). Qed.
Lemma lem7018960 {A : Type'} (f : A -> nat) (x : A) : ((f x) = (NUMERAL 0)) = ((f x) = (NUMERAL 0)).
Proof. exact (eq_refl ((f x) = (NUMERAL 0))). Qed.
Lemma lem7018961 {A : Type'} (x : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) (x' : A) : (term119 A x s t1 t2 f x') = (term120 A x s t1 t2 f x').
Proof. exact (MK_COMB (@lem7018957 A x s t1 x' t2) (@lem7018960 A f x')). Qed.
Lemma lem7018964 {A : Type'} (x : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) : (term121 A x s t1 t2 f) = (term122 A x s t1 t2 f).
Proof. exact (fun_ext (fun x' : A => @lem7018961 A x s t1 t2 f x')). Qed.
Lemma lem7018965 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7018966 {A : Type'} (x : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) : (term123 A x s t1 t2 f) = (term124 A x s t1 t2 f).
Proof. exact (MK_COMB (@lem7018965 A) (@lem7018964 A x s t1 t2 f)). Qed.
Lemma lem7018971 {A : Type'} (x : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> nat) : (term125 A x s t1 f) = (term126 A x s t1 f).
Proof. exact (fun_ext (fun t2 : A -> Prop => @lem7018966 A x s t1 t2 f)). Qed.
Lemma lem7018972 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7018973 {A : Type'} (x : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> nat) : (term127 A x s t1 f) = (term128 A x s t1 f).
Proof. exact (MK_COMB (@lem7018972 A) (@lem7018971 A x s t1 f)). Qed.
Lemma lem7018978 {A : Type'} (x : A -> Prop) (s : type686 A) (f : A -> nat) : (term129 A x s f) = (term130 A x s f).
Proof. exact (fun_ext (fun t1 : A -> Prop => @lem7018973 A x s t1 f)). Qed.
Lemma lem7018979 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7018980 {A : Type'} (x : A -> Prop) (s : type686 A) (f : A -> nat) : (term131 A x s f) = (term132 A x s f).
Proof. exact (MK_COMB (@lem7018979 A) (@lem7018978 A x s f)). Qed.
Lemma lem7018985 {A : Type'} (x : A -> Prop) (s : type686 A) (f : A -> nat) : (term133 A x s f) = (term134 A x s f).
Proof. exact (MK_COMB (@lem7018904 A x s) (@lem7018980 A x s f)). Qed.
Lemma lem7018988 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7018989 {A : Type'} (x : A -> Prop) (s : type686 A) (f : A -> nat) : (term135 A x s f) = (term136 A x s f).
Proof. exact (MK_COMB (@lem7018988) (@lem7018985 A x s f)). Qed.
Lemma lem7018993 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : (term137 _86841 s u) = (term138 _86841 s u).
Proof. exact (EQ_MP (@lem3324017 _86841 s u) (@lem3325374 _86841 s u)). Qed.
Lemma lem7018994 {A : Type'} (s : A -> Prop) (u : type686 A) : (term137 A s u) = (term138 A s u).
Proof. exact (@lem7018993 A s u). Qed.
Lemma lem7018995 {A : Type'} (x : A -> Prop) (s : type686 A) : (term137 A x s) = (term138 A x s).
Proof. exact (@lem7018994 A x s). Qed.
Lemma lem7018996 {A : Type'} : (@nsum A) = (@nsum A).
Proof. exact (eq_refl (@nsum A)). Qed.
Lemma lem7018997 {A : Type'} (x : A -> Prop) (s : type686 A) : (term139 A x s) = (term140 A x s).
Proof. exact (MK_COMB (@lem7018996 A) (@lem7018995 A x s)). Qed.
Lemma lem7018998 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7018999 {A : Type'} (x : A -> Prop) (s : type686 A) (f : A -> nat) : (term141 A x s f) = (term142 A x s f).
Proof. exact (MK_COMB (@lem7018997 A x s) (@lem7018998 A f)). Qed.
Lemma lem7019000 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7019001 {A : Type'} (x : A -> Prop) (s : type686 A) (f : A -> nat) : (term143 A x s f) = (term144 A x s f).
Proof. exact (MK_COMB (@lem7019000) (@lem7018999 A x s f)). Qed.
Lemma lem7019002 {A : Type'} (x : A -> Prop) (s : type686 A) (f : A -> nat) : (term145 A x s f) = (term145 A x s f).
Proof. exact (eq_refl (term145 A x s f)). Qed.
Lemma lem7019003 {A : Type'} (x : A -> Prop) (s : type686 A) (f : A -> nat) : ((term141 A x s f) = (term145 A x s f)) = ((term142 A x s f) = (term145 A x s f)).
Proof. exact (MK_COMB (@lem7019001 A x s f) (@lem7019002 A x s f)). Qed.
Lemma lem7019006 {A : Type'} (x : A -> Prop) (s : type686 A) (f : A -> nat) : (term69 A x s f) = (term146 A x s f).
Proof. exact (MK_COMB (@lem7018989 A x s f) (@lem7019003 A x s f)). Qed.
Lemma lem7019009 {A : Type'} (f : A -> nat) (x : A -> Prop) (s : type686 A) : (term67 A f x s) = (term67 A f x s).
Proof. exact (eq_refl (term67 A f x s)). Qed.
Lemma lem7019010 {A : Type'} (x : A -> Prop) (s : type686 A) (f : A -> nat) : (term71 A x s f) = (term147 A x s f).
Proof. exact (MK_COMB (@lem7019009 A f x s) (@lem7019006 A x s f)). Qed.
Lemma lem7019013 {A : Type'} (x : A -> Prop) (f : A -> nat) : (term73 A x f) = (term148 A x f).
Proof. exact (fun_ext (fun s : type686 A => @lem7019010 A x s f)). Qed.
Lemma lem7019014 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem7019015 {A : Type'} (x : A -> Prop) (f : A -> nat) : (term75 A x f) = (term149 A x f).
Proof. exact (MK_COMB (@lem7019014 A) (@lem7019013 A x f)). Qed.
Lemma lem7019020 {A : Type'} (f : A -> nat) : (term77 A f) = (term150 A f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem7019015 A x f)). Qed.
Lemma lem7019021 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7019022 {A : Type'} (f : A -> nat) : (term79 A f) = (term151 A f).
Proof. exact (MK_COMB (@lem7019021 A) (@lem7019020 A f)). Qed.
Lemma lem7019027 {A : Type'} (f : A -> nat) : (term81 A f) = (term152 A f).
Proof. exact (MK_COMB (@lem7018819 A f) (@lem7019022 A f)). Qed.
Lemma lem7019029 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7019030 {A : Type'} (f : A -> nat) : (term152 A f) = (term151 A f).
Proof. exact (@lem7019029 (term151 A f)). Qed.
Lemma lem7019133 {A : Type'} (f : A -> nat) : (term81 A f) = (term151 A f).
Proof. exact (TRANS (@lem7019027 A f) (@lem7019030 A f)). Qed.
Lemma lem7019134 {A : Type'} (f : A -> nat) : (term151 A f) = (term81 A f).
Proof. exact (SYM (@lem7019133 A f)). Qed.
Lemma lem7019135 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term65 A f t s) : term65 A f t s.
Proof. exact (h1). Qed.
Lemma lem7019136 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term134 A t s f) : term134 A t s f.
Proof. exact (h1). Qed.
Lemma lem7019137 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term132 A t s f.
Proof. exact (h1). Qed.
Lemma lem7019138 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : term107 A t s.
Proof. exact (h1). Qed.
Lemma lem7019140 (p : Prop) (q : Prop) (r : Prop) : (term41 p q r) = (term42 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7019141 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term153 A t s f) = (term154 A t s f).
Proof. exact (@lem7019140 (term60 A s f) (term63 A t s) ((term142 A t s f) = (term145 A t s f))). Qed.
Lemma lem7019142 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term154 A t s f) = (term153 A t s f).
Proof. exact (SYM (@lem7019141 A t s f)). Qed.
Lemma lem7019143 {_126525 : Type'} : term155 _126525.
Proof. exact (proj2 (@lem6924916 Prop _126525)). Qed.
Lemma lem7019144 {_126525 : Type'} (x : _126525) : term156 _126525 x.
Proof. exact (@lem7019143 _126525 x). Qed.
Lemma lem7019145 {_126525 : Type'} (x : _126525) : (term156 _126525 x) = (term157 _126525 x).
Proof. exact (eq_refl (term156 _126525 x)). Qed.
Lemma lem7019146 {_126525 : Type'} (x : _126525) : term157 _126525 x.
Proof. exact (EQ_MP (@lem7019145 _126525 x) (@lem7019144 _126525 x)). Qed.
Lemma lem7019147 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : term158 _126525 x f.
Proof. exact (@lem7019146 _126525 x f). Qed.
Lemma lem7019148 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : (term158 _126525 x f) = (term159 _126525 x f).
Proof. exact (eq_refl (term158 _126525 x f)). Qed.
Lemma lem7019149 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : term159 _126525 x f.
Proof. exact (EQ_MP (@lem7019148 _126525 x f) (@lem7019147 _126525 x f)). Qed.
Lemma lem7019150 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) (s : _126525 -> Prop) : term160 _126525 x f s.
Proof. exact (@lem7019149 _126525 x f s). Qed.
Lemma lem7019151 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : (term160 _126525 x f s) = (term161 _126525 x s f).
Proof. exact (eq_refl (term160 _126525 x f s)). Qed.
Lemma lem7019152 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term161 _126525 x s f.
Proof. exact (EQ_MP (@lem7019151 _126525 x s f) (@lem7019150 _126525 x f s)). Qed.
Lemma lem7019153 {_126525 : Type'} (s : _126525 -> Prop) (h1 : @FINITE _126525 s) : @FINITE _126525 s.
Proof. exact (h1). Qed.
Lemma lem7019154 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) (s : _126525 -> Prop) (h1 : @FINITE _126525 s) : (term162 _126525 x s f) = (term163 _126525 x s f).
Proof. exact (@lem7019152 _126525 x s f (@lem7019153 _126525 s h1)). Qed.
Lemma lem7019164 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : term164 A t s t'.
Proof. exact (@lem7019138 A t s h1 t'). Qed.
Lemma lem7019165 {A : Type'} (t : A -> Prop) (s : type686 A) (t' : A -> Prop) : (term164 A t s t') = (term103 A t s t').
Proof. exact (eq_refl (term164 A t s t')). Qed.
Lemma lem7019166 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : term103 A t s t'.
Proof. exact (EQ_MP (@lem7019165 A t s t') (@lem7019164 A t' t s h1)). Qed.
Lemma lem7019167 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (s : type686 A) (h1 : term99 A t t' s) : term99 A t t' s.
Proof. exact (h1). Qed.
Lemma lem7019168 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (s : type686 A) (h1 : term107 A t s) (h2 : term99 A t t' s) : @FINITE A t'.
Proof. exact (@lem7019166 A t' t s h1 (@lem7019167 A t t' s h2)). Qed.
Lemma lem7019169 {A : Type'} (t' : A -> Prop) : (@FINITE A t') = ((@FINITE A t') = True).
Proof. exact (@lem7 (@FINITE A t')). Qed.
Lemma lem7019170 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (s : type686 A) (h1 : term107 A t s) (h2 : term99 A t t' s) : (@FINITE A t') = True.
Proof. exact (EQ_MP (@lem7019169 A t') (@lem7019168 A t t' s h1 h2)). Qed.
Lemma lem7019247 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term165 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7019248 (p : Prop) (q : Prop) (p' : Prop) : term166 p q p'.
Proof. exact (fun q' : Prop => @lem7019247 p q p' q'). Qed.
Lemma lem7019249 (p : Prop) (q : Prop) : term167 p q.
Proof. exact (fun p' : Prop => @lem7019248 p q p'). Qed.
Lemma lem7019250 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : term168 A t s f.
Proof. exact (@lem7019249 (term60 A s f) (term169 A t s f)). Qed.
Lemma lem7019251 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (p' : Prop) : term170 A t s f p'.
Proof. exact (@lem7019250 A t s f p'). Qed.
Lemma lem7019252 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (p' : Prop) : (term170 A t s f p') = (term171 A t s f p').
Proof. exact (eq_refl (term170 A t s f p')). Qed.
Lemma lem7019253 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (p' : Prop) : term171 A t s f p'.
Proof. exact (EQ_MP (@lem7019252 A t s f p') (@lem7019251 A t s f p')). Qed.
Lemma lem7019254 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (p' : Prop) (q' : Prop) : term172 A t s f p' q'.
Proof. exact (@lem7019253 A t s f p' q'). Qed.
Lemma lem7019255 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (p' : Prop) (q' : Prop) : (term172 A t s f p' q') = (term173 A t s f p' q').
Proof. exact (eq_refl (term172 A t s f p' q')). Qed.
Lemma lem7019256 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (p' : Prop) (q' : Prop) : term173 A t s f p' q'.
Proof. exact (EQ_MP (@lem7019255 A t s f p' q') (@lem7019254 A t s f p' q')). Qed.
Lemma lem7019260 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term165 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7019261 (p : Prop) (q : Prop) (p' : Prop) : term166 p q p'.
Proof. exact (fun q' : Prop => @lem7019260 p q p' q'). Qed.
Lemma lem7019262 (p : Prop) (q : Prop) : term167 p q.
Proof. exact (fun p' : Prop => @lem7019261 p q p'). Qed.
Lemma lem7019263 {A : Type'} (s : type686 A) (f : A -> nat) : term174 A s f.
Proof. exact (@lem7019262 (term45 A s f) ((term46 A s f) = (term47 A s f))). Qed.
Lemma lem7019264 {A : Type'} (s : type686 A) (f : A -> nat) (p' : Prop) : term175 A s f p'.
Proof. exact (@lem7019263 A s f p'). Qed.
Lemma lem7019265 {A : Type'} (s : type686 A) (f : A -> nat) (p' : Prop) : (term175 A s f p') = (term176 A s f p').
Proof. exact (eq_refl (term175 A s f p')). Qed.
Lemma lem7019266 {A : Type'} (s : type686 A) (f : A -> nat) (p' : Prop) : term176 A s f p'.
Proof. exact (EQ_MP (@lem7019265 A s f p') (@lem7019264 A s f p')). Qed.
Lemma lem7019267 {A : Type'} (s : type686 A) (f : A -> nat) (p' : Prop) (q' : Prop) : term177 A s f p' q'.
Proof. exact (@lem7019266 A s f p' q'). Qed.
Lemma lem7019268 {A : Type'} (s : type686 A) (f : A -> nat) (p' : Prop) (q' : Prop) : (term177 A s f p' q') = (term178 A s f p' q').
Proof. exact (eq_refl (term177 A s f p' q')). Qed.
Lemma lem7019269 {A : Type'} (s : type686 A) (f : A -> nat) (p' : Prop) (q' : Prop) : term178 A s f p' q'.
Proof. exact (EQ_MP (@lem7019268 A s f p' q') (@lem7019267 A s f p' q')). Qed.
Lemma lem7019327 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term165 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7019328 (p : Prop) (q : Prop) (p' : Prop) : term166 p q p'.
Proof. exact (fun q' : Prop => @lem7019327 p q p' q'). Qed.
Lemma lem7019329 (p : Prop) (q : Prop) : term167 p q.
Proof. exact (fun p' : Prop => @lem7019328 p q p'). Qed.
Lemma lem7019330 {A : Type'} (s : type686 A) (_93779 : A -> Prop) : term179 A s _93779.
Proof. exact (@lem7019329 (@IN (A -> Prop) _93779 s) (@FINITE A _93779)). Qed.
Lemma lem7019331 {A : Type'} (s : type686 A) (_93779 : A -> Prop) (p' : Prop) : term180 A s _93779 p'.
Proof. exact (@lem7019330 A s _93779 p'). Qed.
Lemma lem7019332 {A : Type'} (s : type686 A) (_93779 : A -> Prop) (p' : Prop) : (term180 A s _93779 p') = (term181 A s _93779 p').
Proof. exact (eq_refl (term180 A s _93779 p')). Qed.
Lemma lem7019333 {A : Type'} (s : type686 A) (_93779 : A -> Prop) (p' : Prop) : term181 A s _93779 p'.
Proof. exact (EQ_MP (@lem7019332 A s _93779 p') (@lem7019331 A s _93779 p')). Qed.
Lemma lem7019334 {A : Type'} (s : type686 A) (_93779 : A -> Prop) (p' : Prop) (q' : Prop) : term182 A s _93779 p' q'.
Proof. exact (@lem7019333 A s _93779 p' q'). Qed.
Lemma lem7019335 {A : Type'} (s : type686 A) (_93779 : A -> Prop) (p' : Prop) (q' : Prop) : (term182 A s _93779 p' q') = (term183 A s _93779 p' q').
Proof. exact (eq_refl (term182 A s _93779 p' q')). Qed.
Lemma lem7019336 {A : Type'} (s : type686 A) (_93779 : A -> Prop) (p' : Prop) (q' : Prop) : term183 A s _93779 p' q'.
Proof. exact (EQ_MP (@lem7019335 A s _93779 p' q') (@lem7019334 A s _93779 p' q')). Qed.
Lemma lem7019337 {A : Type'} (_93779 : A -> Prop) (s : type686 A) : (@IN (A -> Prop) _93779 s) = (@IN (A -> Prop) _93779 s).
Proof. exact (eq_refl (@IN (A -> Prop) _93779 s)). Qed.
Lemma lem7019338 {A : Type'} (_93779 : A -> Prop) (s : type686 A) (q' : Prop) : term184 A _93779 s q'.
Proof. exact (@lem7019336 A s _93779 (@IN (A -> Prop) _93779 s) q'). Qed.
Lemma lem7019339 {A : Type'} (_93779 : A -> Prop) (s : type686 A) (q' : Prop) : term185 A _93779 s q'.
Proof. exact (@lem7019338 A _93779 s q' (@lem7019337 A _93779 s)). Qed.
Lemma lem7019340 {A : Type'} (_93779 : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) _93779 s) : @IN (A -> Prop) _93779 s.
Proof. exact (h1). Qed.
Lemma lem7019341 {A : Type'} (_93779 : A -> Prop) (s : type686 A) : (@IN (A -> Prop) _93779 s) = ((@IN (A -> Prop) _93779 s) = True).
Proof. exact (@lem7 (@IN (A -> Prop) _93779 s)). Qed.
Lemma lem7019344 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : term186 A t s t'.
Proof. exact (fun h0 : term99 A t t' s => @lem7019170 A t t' s h1 h0). Qed.
Lemma lem7019345 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : term186 A t s t'.
Proof. exact (@lem7019344 A t' t s h1). Qed.
Lemma lem7019346 {A : Type'} (_93779 : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : term186 A t s _93779.
Proof. exact (@lem7019345 A _93779 t s h1). Qed.
Lemma lem7019352 {A : Type'} (_93779 : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) _93779 s) : (@IN (A -> Prop) _93779 s) = True.
Proof. exact (EQ_MP (@lem7019341 A _93779 s) (@lem7019340 A _93779 s h1)). Qed.
Lemma lem7019353 {A : Type'} (_93779 : A -> Prop) (t : A -> Prop) : (term187 A _93779 t) = (term187 A _93779 t).
Proof. exact (eq_refl (term187 A _93779 t)). Qed.
Lemma lem7019354 {A : Type'} (t : A -> Prop) (_93779 : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) _93779 s) : (term99 A t _93779 s) = (term188 A _93779 t).
Proof. exact (MK_COMB (@lem7019353 A _93779 t) (@lem7019352 A _93779 s h1)). Qed.
Lemma lem7019356 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem7019357 {A : Type'} (_93779 : A -> Prop) (t : A -> Prop) : (term188 A _93779 t) = True.
Proof. exact (@lem7019356 (_93779 = t)). Qed.
Lemma lem7019358 {A : Type'} (t : A -> Prop) (_93779 : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) _93779 s) : (term99 A t _93779 s) = True.
Proof. exact (TRANS (@lem7019354 A t _93779 s h1) (@lem7019357 A _93779 t)). Qed.
Lemma lem7019359 {A : Type'} (t : A -> Prop) (_93779 : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) _93779 s) : True = (term99 A t _93779 s).
Proof. exact (SYM (@lem7019358 A t _93779 s h1)). Qed.
Lemma lem7019360 {A : Type'} (t : A -> Prop) (_93779 : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) _93779 s) : term99 A t _93779 s.
Proof. exact (EQ_MP (@lem7019359 A t _93779 s h1) (@lem0)). Qed.
Lemma lem7019361 {A : Type'} (t : A -> Prop) (_93779 : A -> Prop) (s : type686 A) (h1 : term107 A t s) (h2 : @IN (A -> Prop) _93779 s) : (@FINITE A _93779) = True.
Proof. exact (@lem7019346 A _93779 t s h1 (@lem7019360 A t _93779 s h2)). Qed.
Lemma lem7019362 {A : Type'} (_93779 : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : term189 A s _93779.
Proof. exact (fun h0 : @IN (A -> Prop) _93779 s => @lem7019361 A t _93779 s h1 h0). Qed.
Lemma lem7019363 {A : Type'} (_93779 : A -> Prop) (s : type686 A) : term190 A _93779 s.
Proof. exact (@lem7019339 A _93779 s True). Qed.
Lemma lem7019364 {A : Type'} (_93779 : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : (term191 A s _93779) = (term192 A _93779 s).
Proof. exact (@lem7019363 A _93779 s (@lem7019362 A _93779 t s h1)). Qed.
Lemma lem7019366 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7019367 {A : Type'} (_93779 : A -> Prop) (s : type686 A) : (term192 A _93779 s) = True.
Proof. exact (@lem7019366 (@IN (A -> Prop) _93779 s)). Qed.
Lemma lem7019368 {A : Type'} (_93779 : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : (term191 A s _93779) = True.
Proof. exact (TRANS (@lem7019364 A _93779 t s h1) (@lem7019367 A _93779 s)). Qed.
Lemma lem7019371 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : (term193 A s) = (term194 A).
Proof. exact (fun_ext (fun _93779 : A -> Prop => @lem7019368 A _93779 t s h1)). Qed.
Lemma lem7019372 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7019373 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : (term195 A s) = (term196 A).
Proof. exact (MK_COMB (@lem7019372 A) (@lem7019371 A t s h1)). Qed.
Lemma lem7019375 {A : Type'} (t : Prop) : (term197 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7019376 {A : Type'} (t : Prop) : (term198 A t) = t.
Proof. exact (@lem7019375 (A -> Prop) t). Qed.
Lemma lem7019377 {A : Type'} : (term196 A) = True.
Proof. exact (@lem7019376 A True). Qed.
Lemma lem7019378 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : (term195 A s) = True.
Proof. exact (TRANS (@lem7019373 A t s h1) (@lem7019377 A)). Qed.
Lemma lem7019379 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7019380 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : (term199 A s) = (and True).
Proof. exact (MK_COMB (@lem7019379) (@lem7019378 A t s h1)). Qed.
Lemma lem7019845 {A : Type'} (s : type686 A) (f : A -> nat) : (term200 A s f) = (term200 A s f).
Proof. exact (eq_refl (term200 A s f)). Qed.
Lemma lem7019846 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : (term45 A s f) = (term201 A s f).
Proof. exact (MK_COMB (@lem7019380 A t s h1) (@lem7019845 A s f)). Qed.
Lemma lem7019848 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7019849 {A : Type'} (s : type686 A) (f : A -> nat) : (term201 A s f) = (term200 A s f).
Proof. exact (@lem7019848 (term200 A s f)). Qed.
Lemma lem7020314 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : (term45 A s f) = (term200 A s f).
Proof. exact (TRANS (@lem7019846 A f t s h1) (@lem7019849 A s f)). Qed.
Lemma lem7020315 {A : Type'} (s : type686 A) (f : A -> nat) (q' : Prop) : term202 A s f q'.
Proof. exact (@lem7019269 A s f (term200 A s f) q'). Qed.
Lemma lem7020316 {A : Type'} (f : A -> nat) (q' : Prop) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : term203 A s f q'.
Proof. exact (@lem7020315 A s f q' (@lem7020314 A f t s h1)). Qed.
Lemma lem7020388 {A : Type'} (s : type686 A) (f : A -> nat) : ((term46 A s f) = (term47 A s f)) = ((term46 A s f) = (term47 A s f)).
Proof. exact (eq_refl ((term46 A s f) = (term47 A s f))). Qed.
Lemma lem7020389 {A : Type'} (s : type686 A) (f : A -> nat) : term204 A s f.
Proof. exact (fun h0 : term200 A s f => @lem7020388 A s f). Qed.
Lemma lem7020390 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : term205 A s f.
Proof. exact (@lem7020316 A f ((term46 A s f) = (term47 A s f)) t s h1). Qed.
Lemma lem7020391 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : (term60 A s f) = (term206 A s f).
Proof. exact (@lem7020390 A f t s h1 (@lem7020389 A s f)). Qed.
Lemma lem7021413 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (q' : Prop) : term207 A t s f q'.
Proof. exact (@lem7019256 A t s f (term206 A s f) q'). Qed.
Lemma lem7021414 {A : Type'} (f : A -> nat) (q' : Prop) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : term208 A t s f q'.
Proof. exact (@lem7021413 A t s f q' (@lem7020391 A f t s h1)). Qed.
Lemma lem7021426 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term165 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7021427 (p : Prop) (q : Prop) (p' : Prop) : term166 p q p'.
Proof. exact (fun q' : Prop => @lem7021426 p q p' q'). Qed.
Lemma lem7021428 (p : Prop) (q : Prop) : term167 p q.
Proof. exact (fun p' : Prop => @lem7021427 p q p'). Qed.
Lemma lem7021429 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : term209 A t s f.
Proof. exact (@lem7021428 (term63 A t s) ((term142 A t s f) = (term145 A t s f))). Qed.
Lemma lem7021430 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (p' : Prop) : term210 A t s f p'.
Proof. exact (@lem7021429 A t s f p'). Qed.
Lemma lem7021431 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (p' : Prop) : (term210 A t s f p') = (term211 A t s f p').
Proof. exact (eq_refl (term210 A t s f p')). Qed.
Lemma lem7021432 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (p' : Prop) : term211 A t s f p'.
Proof. exact (EQ_MP (@lem7021431 A t s f p') (@lem7021430 A t s f p')). Qed.
Lemma lem7021433 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (p' : Prop) (q' : Prop) : term212 A t s f p' q'.
Proof. exact (@lem7021432 A t s f p' q'). Qed.
Lemma lem7021434 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (p' : Prop) (q' : Prop) : (term212 A t s f p' q') = (term213 A t s f p' q').
Proof. exact (eq_refl (term212 A t s f p' q')). Qed.
Lemma lem7021435 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (p' : Prop) (q' : Prop) : term213 A t s f p' q'.
Proof. exact (EQ_MP (@lem7021434 A t s f p' q') (@lem7021433 A t s f p' q')). Qed.
Lemma lem7021442 {A : Type'} (t : A -> Prop) (s : type686 A) : (term63 A t s) = (term63 A t s).
Proof. exact (eq_refl (term63 A t s)). Qed.
Lemma lem7021443 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (q' : Prop) : term214 A f t s q'.
Proof. exact (@lem7021435 A t s f (term63 A t s) q'). Qed.
Lemma lem7021444 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (q' : Prop) : term215 A f t s q'.
Proof. exact (@lem7021443 A f t s q' (@lem7021442 A t s)). Qed.
Lemma lem7021445 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term63 A t s) : term63 A t s.
Proof. exact (h1). Qed.
Lemma lem7021446 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term63 A t s) : @FINITE (A -> Prop) s.
Proof. exact (proj2 (@lem7021445 A t s h1)). Qed.
Lemma lem7021447 {A : Type'} (s : type686 A) : (@FINITE (A -> Prop) s) = ((@FINITE (A -> Prop) s) = True).
Proof. exact (@lem7 (@FINITE (A -> Prop) s)). Qed.
Lemma lem7021449 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term63 A t s) : term216 A t s.
Proof. exact (proj1 (@lem7021445 A t s h1)). Qed.
Lemma lem7021450 {A : Type'} (t : A -> Prop) (s : type686 A) : term217 A t s.
Proof. exact (@lem82 (@IN (A -> Prop) t s)). Qed.
Lemma lem7021455 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term161 _126525 x s f.
Proof. exact (fun h0 : @FINITE _126525 s => @lem7019154 _126525 x f s h0). Qed.
Lemma lem7021456 {A : Type'} (x : A -> Prop) (s : type686 A) (f : type687 A) : term218 A x s f.
Proof. exact (@lem7021455 (A -> Prop) x s f). Qed.
Lemma lem7021457 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : term219 A t s f.
Proof. exact (@lem7021456 A t s (term94 A f)). Qed.
Lemma lem7021459 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term63 A t s) : (@FINITE (A -> Prop) s) = True.
Proof. exact (EQ_MP (@lem7021447 A s) (@lem7021446 A t s h1)). Qed.
Lemma lem7021460 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term63 A t s) : True = (@FINITE (A -> Prop) s).
Proof. exact (SYM (@lem7021459 A t s h1)). Qed.
Lemma lem7021461 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term63 A t s) : @FINITE (A -> Prop) s.
Proof. exact (EQ_MP (@lem7021460 A t s h1) (@lem0)). Qed.
Lemma lem7021462 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term63 A t s) : (term145 A t s f) = (term220 A t s f).
Proof. exact (@lem7021457 A t s f (@lem7021461 A t s h1)). Qed.
Lemma lem7021464 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term221 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7021465 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term222 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7021464 _2963 g t e g' t' e'). Qed.
Lemma lem7021466 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term223 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7021465 _2963 g t e g' t'). Qed.
Lemma lem7021467 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term224 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7021466 _2963 g t e g'). Qed.
Lemma lem7021468 (g : Prop) (t : nat) (e : nat) : term225 g t e.
Proof. exact (@lem7021467 nat g t e). Qed.
Lemma lem7021469 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : term226 A t s f.
Proof. exact (@lem7021468 (@IN (A -> Prop) t s) (term47 A s f) (term227 A t s f)). Qed.
Lemma lem7021470 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (g' : Prop) : term228 A t s f g'.
Proof. exact (@lem7021469 A t s f g'). Qed.
Lemma lem7021471 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (g' : Prop) : (term228 A t s f g') = (term229 A t s f g').
Proof. exact (eq_refl (term228 A t s f g')). Qed.
Lemma lem7021472 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (g' : Prop) : term229 A t s f g'.
Proof. exact (EQ_MP (@lem7021471 A t s f g') (@lem7021470 A t s f g')). Qed.
Lemma lem7021473 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (g' : Prop) (t' : nat) : term230 A t s f g' t'.
Proof. exact (@lem7021472 A t s f g' t'). Qed.
Lemma lem7021474 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (g' : Prop) (t' : nat) : (term230 A t s f g' t') = (term231 A t s f g' t').
Proof. exact (eq_refl (term230 A t s f g' t')). Qed.
Lemma lem7021475 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (g' : Prop) (t' : nat) : term231 A t s f g' t'.
Proof. exact (EQ_MP (@lem7021474 A t s f g' t') (@lem7021473 A t s f g' t')). Qed.
Lemma lem7021476 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (g' : Prop) (t' : nat) (e' : nat) : term232 A t s f g' t' e'.
Proof. exact (@lem7021475 A t s f g' t' e'). Qed.
Lemma lem7021477 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (g' : Prop) (t' : nat) (e' : nat) : (term232 A t s f g' t' e') = (term233 A t s f g' t' e').
Proof. exact (eq_refl (term232 A t s f g' t' e')). Qed.
Lemma lem7021478 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (g' : Prop) (t' : nat) (e' : nat) : term233 A t s f g' t' e'.
Proof. exact (EQ_MP (@lem7021477 A t s f g' t' e') (@lem7021476 A t s f g' t' e')). Qed.
Lemma lem7021480 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term63 A t s) : (@IN (A -> Prop) t s) = False.
Proof. exact (@lem7021450 A t s (@lem7021449 A t s h1)). Qed.
Lemma lem7021481 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (t' : nat) (e' : nat) : term234 A t s f t' e'.
Proof. exact (@lem7021478 A t s f False t' e'). Qed.
Lemma lem7021482 {A : Type'} (f : A -> nat) (t' : nat) (e' : nat) (t : A -> Prop) (s : type686 A) (h1 : term63 A t s) : term235 A t s f t' e'.
Proof. exact (@lem7021481 A t s f t' e' (@lem7021480 A t s h1)). Qed.
Lemma lem7021486 {A : Type'} (s : type686 A) (f : A -> nat) : (term47 A s f) = (term47 A s f).
Proof. exact (eq_refl (term47 A s f)). Qed.
Lemma lem7021487 {A : Type'} (s : type686 A) (f : A -> nat) : term236 A s f.
Proof. exact (fun h0 : False => @lem7021486 A s f). Qed.
Lemma lem7021488 {A : Type'} (f : A -> nat) (e' : nat) (t : A -> Prop) (s : type686 A) (h1 : term63 A t s) : term237 A t s f e'.
Proof. exact (@lem7021482 A f (term47 A s f) e' t s h1). Qed.
Lemma lem7021489 {A : Type'} (f : A -> nat) (e' : nat) (t : A -> Prop) (s : type686 A) (h1 : term63 A t s) : term238 A t s f e'.
Proof. exact (@lem7021488 A f e' t s h1 (@lem7021487 A s f)). Qed.
Lemma lem7021496 {A B : Type'} (f : A -> B) (y : A) : (term239 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7021497 {A : Type'} (f : type687 A) (y : A -> Prop) : (term240 A f y) = (f y).
Proof. exact (@lem7021496 (A -> Prop) nat f y). Qed.
Lemma lem7021498 {A : Type'} (f : A -> nat) (t : A -> Prop) : (term241 A f t) = (term242 A f t).
Proof. exact (@lem7021497 A (term94 A f) t). Qed.
Lemma lem7021499 {A : Type'} (t : A -> Prop) (f : A -> nat) : (term242 A f t) = (@nsum A t f).
Proof. exact (eq_refl (term242 A f t)). Qed.
Lemma lem7021500 {A : Type'} (f : A -> nat) : (term243 A f) = (term94 A f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7021499 A t f)). Qed.
Lemma lem7021501 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7021502 {A : Type'} (f : A -> nat) (t : A -> Prop) : (term241 A f t) = (term242 A f t).
Proof. exact (MK_COMB (@lem7021500 A f) (@lem7021501 A t)). Qed.
Lemma lem7021503 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7021504 {A : Type'} (f : A -> nat) (t : A -> Prop) : (term244 A f t) = (term245 A f t).
Proof. exact (MK_COMB (@lem7021503) (@lem7021502 A f t)). Qed.
Lemma lem7021505 {A : Type'} (t : A -> Prop) (f : A -> nat) : (term242 A f t) = (@nsum A t f).
Proof. exact (eq_refl (term242 A f t)). Qed.
Lemma lem7021506 {A : Type'} (t : A -> Prop) (f : A -> nat) : ((term241 A f t) = (term242 A f t)) = ((term242 A f t) = (@nsum A t f)).
Proof. exact (MK_COMB (@lem7021504 A f t) (@lem7021505 A t f)). Qed.
Lemma lem7021507 {A : Type'} (t : A -> Prop) (f : A -> nat) : (term242 A f t) = (@nsum A t f).
Proof. exact (EQ_MP (@lem7021506 A t f) (@lem7021498 A f t)). Qed.
Lemma lem7021508 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem7021509 {A : Type'} (t : A -> Prop) (f : A -> nat) : (term246 A f t) = (term247 A t f).
Proof. exact (MK_COMB (@lem7021508) (@lem7021507 A t f)). Qed.
Lemma lem7021510 {A : Type'} (s : type686 A) (f : A -> nat) : (term47 A s f) = (term47 A s f).
Proof. exact (eq_refl (term47 A s f)). Qed.
Lemma lem7021511 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term227 A t s f) = (term248 A t s f).
Proof. exact (MK_COMB (@lem7021509 A t f) (@lem7021510 A s f)). Qed.
Lemma lem7021512 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : term249 A t s f.
Proof. exact (fun h0 : ~ False => @lem7021511 A t s f). Qed.
Lemma lem7021513 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term63 A t s) : term250 A t s f.
Proof. exact (@lem7021489 A f (term248 A t s f) t s h1). Qed.
Lemma lem7021514 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term63 A t s) : (term220 A t s f) = (term251 A t s f).
Proof. exact (@lem7021513 A f t s h1 (@lem7021512 A t s f)). Qed.
Lemma lem7021516 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7021517 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem7021516 nat t1 t2). Qed.
Lemma lem7021518 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term251 A t s f) = (term248 A t s f).
Proof. exact (@lem7021517 (term47 A s f) (term248 A t s f)). Qed.
Lemma lem7021519 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term63 A t s) : (term220 A t s f) = (term248 A t s f).
Proof. exact (TRANS (@lem7021514 A f t s h1) (@lem7021518 A t s f)). Qed.
Lemma lem7021520 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term63 A t s) : (term145 A t s f) = (term248 A t s f).
Proof. exact (TRANS (@lem7021462 A f t s h1) (@lem7021519 A f t s h1)). Qed.
Lemma lem7021521 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term144 A t s f) = (term144 A t s f).
Proof. exact (eq_refl (term144 A t s f)). Qed.
Lemma lem7021522 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term63 A t s) : ((term142 A t s f) = (term145 A t s f)) = ((term142 A t s f) = (term248 A t s f)).
Proof. exact (MK_COMB (@lem7021521 A t s f) (@lem7021520 A f t s h1)). Qed.
Lemma lem7021525 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : term252 A t s f.
Proof. exact (fun h0 : term63 A t s => @lem7021522 A f t s h0). Qed.
Lemma lem7021526 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : term253 A t s f.
Proof. exact (@lem7021444 A f t s ((term142 A t s f) = (term248 A t s f))). Qed.
Lemma lem7021527 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term169 A t s f) = (term254 A t s f).
Proof. exact (@lem7021526 A t s f (@lem7021525 A t s f)). Qed.
Lemma lem7021571 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : term255 A t s f.
Proof. exact (fun h0 : term206 A s f => @lem7021527 A t s f). Qed.
Lemma lem7021572 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : term256 A t s f.
Proof. exact (@lem7021414 A f (term254 A t s f) t s h1). Qed.
Lemma lem7021573 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : (term154 A t s f) = (term257 A t s f).
Proof. exact (@lem7021572 A f t s h1 (@lem7021571 A t s f)). Qed.
Lemma lem7023730 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : (term257 A t s f) = (term154 A t s f).
Proof. exact (SYM (@lem7021573 A f t s h1)). Qed.
Lemma lem7023732 (p : Prop) (q : Prop) (r : Prop) : term258 p q r.
Proof. exact (@lem137 p q r (@lem129 p q r)). Qed.
Lemma lem7023733 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : term259 A t s f.
Proof. exact (@lem7023732 (term200 A s f) ((term46 A s f) = (term47 A s f)) (term254 A t s f)). Qed.
Lemma lem7023735 (p : Prop) : p = (term260 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7023736 {A : Type'} (s : type686 A) (f : A -> nat) : (term200 A s f) = (term261 A s f).
Proof. exact (@lem7023735 (term200 A s f)). Qed.
Lemma lem7023737 {A : Type'} (s : type686 A) (f : A -> nat) : (term261 A s f) = (term200 A s f).
Proof. exact (SYM (@lem7023736 A s f)). Qed.
Lemma lem7023738 {A : Type'} (s : type686 A) (f : A -> nat) (h1 : term262 A s f) : term262 A s f.
Proof. exact (h1). Qed.
Lemma lem7023741 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term263 A t s f) : term263 A t s f.
Proof. exact (h1). Qed.
Lemma lem7023742 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : term264 A t s f.
Proof. exact (fun h0 : term263 A t s f => @lem7023741 A t s f h0). Qed.
Lemma lem7023743 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term264 A t s f) : term264 A t s f.
Proof. exact (h1). Qed.
Lemma lem7023744 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term263 A t s f) : term263 A t s f.
Proof. exact (h1). Qed.
Lemma lem7023745 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term263 A t s f) (h2 : term264 A t s f) : term263 A t s f.
Proof. exact (@lem7023743 A t s f h2 (@lem7023744 A t s f h1)). Qed.
Lemma lem7023746 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term263 A t s f) : term265 A t s f.
Proof. exact (fun h0 : term264 A t s f => @lem7023745 A t s f h1 h0). Qed.
Lemma lem7023747 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term264 A t s f) : term264 A t s f.
Proof. exact (h1). Qed.
Lemma lem7023748 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term263 A t s f) (h2 : term264 A t s f) : term263 A t s f.
Proof. exact (@lem7023746 A t s f h1 (@lem7023747 A t s f h2)). Qed.
Lemma lem7023749 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term264 A t s f) : term264 A t s f.
Proof. exact (fun h0 : term263 A t s f => @lem7023748 A t s f h0 h1). Qed.
Lemma lem7023750 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : term266 A t s f.
Proof. exact (fun h0 : term264 A t s f => @lem7023749 A t s f h0). Qed.
Lemma lem7023753 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : term264 A t s f.
Proof. exact (@lem7023750 A t s f (@lem7023742 A t s f)). Qed.
Lemma lem7023754 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : term264 A t s f.
Proof. exact (@lem7023753 A t s f). Qed.
Lemma lem7023806 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7023807 {A : Type'} (s : type686 A) (f : A -> nat) : (term261 A s f) = (term267 A s f).
Proof. exact (@lem7023806 (term262 A s f)). Qed.
Lemma lem7023809 (t : Prop) : (term268 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7023810 {A : Type'} (s : type686 A) (f : A -> nat) : (term267 A s f) = (term200 A s f).
Proof. exact (@lem7023809 (term200 A s f)). Qed.
Lemma lem7023815 {A : Type'} (s : type686 A) (f : A -> nat) : (term261 A s f) = (term200 A s f).
Proof. exact (TRANS (@lem7023807 A s f) (@lem7023810 A s f)). Qed.
Lemma lem7023834 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term269 A t s f) = (term269 A t s f).
Proof. exact (eq_refl (term269 A t s f)). Qed.
Lemma lem7023835 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term270 A t s f) = (term271 A t s f).
Proof. exact (MK_COMB (@lem7023834 A t s f) (@lem7023815 A s f)). Qed.
Lemma lem7023838 {A : Type'} (t : A -> Prop) (s : type686 A) : (term272 A t s) = (term272 A t s).
Proof. exact (eq_refl (term272 A t s)). Qed.
Lemma lem7023839 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term263 A t s f) = (term273 A t s f).
Proof. exact (MK_COMB (@lem7023838 A t s) (@lem7023835 A t s f)). Qed.
Lemma lem7023842 {A : Type'} (s : type686 A) (f : A -> nat) : (term274 A s f) = (term275 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7023839 A t s f)). Qed.
Lemma lem7023843 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7023844 {A : Type'} (s : type686 A) (f : A -> nat) : (term276 A s f) = (term277 A s f).
Proof. exact (MK_COMB (@lem7023843 A) (@lem7023842 A s f)). Qed.
Lemma lem7023849 {A : Type'} (f : A -> nat) : (term278 A f) = (term279 A f).
Proof. exact (fun_ext (fun s : type686 A => @lem7023844 A s f)). Qed.
Lemma lem7023850 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem7023851 {A : Type'} (f : A -> nat) : (term280 A f) = (term281 A f).
Proof. exact (MK_COMB (@lem7023850 A) (@lem7023849 A f)). Qed.
Lemma lem7023856 {A : Type'} : (term282 A) = (term283 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem7023851 A f)). Qed.
Lemma lem7023857 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7023866 {A : Type'} : (term284 A) = (term285 A).
Proof. exact (MK_COMB (@lem7023857 A) (@lem7023856 A)). Qed.
Lemma lem7023889 {A : Type'} (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) (x : A) : (term286 A s t1 t2 f x) = (term286 A s t1 t2 f x).
Proof. exact (eq_refl (term286 A s t1 t2 f x)). Qed.
Lemma lem7023890 {A : Type'} (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) : (term287 A s t1 t2 f) = (term287 A s t1 t2 f).
Proof. exact (fun_ext (fun x : A => @lem7023889 A s t1 t2 f x)). Qed.
Lemma lem7023891 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7023892 {A : Type'} (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) : (term288 A s t1 t2 f) = (term288 A s t1 t2 f).
Proof. exact (MK_COMB (@lem7023891 A) (@lem7023890 A s t1 t2 f)). Qed.
Lemma lem7023893 {A : Type'} (s : type686 A) (t1 : A -> Prop) (f : A -> nat) : (term289 A s t1 f) = (term289 A s t1 f).
Proof. exact (fun_ext (fun t2 : A -> Prop => @lem7023892 A s t1 t2 f)). Qed.
Lemma lem7023894 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7023895 {A : Type'} (s : type686 A) (t1 : A -> Prop) (f : A -> nat) : (term290 A s t1 f) = (term290 A s t1 f).
Proof. exact (MK_COMB (@lem7023894 A) (@lem7023893 A s t1 f)). Qed.
Lemma lem7023896 {A : Type'} (s : type686 A) (f : A -> nat) : (term291 A s f) = (term291 A s f).
Proof. exact (fun_ext (fun t1 : A -> Prop => @lem7023895 A s t1 f)). Qed.
Lemma lem7023897 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7023898 {A : Type'} (s : type686 A) (f : A -> nat) : (term200 A s f) = (term200 A s f).
Proof. exact (MK_COMB (@lem7023897 A) (@lem7023896 A s f)). Qed.
Lemma lem7023929 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) (x : A) : (term120 A t s t1 t2 f x) = (term120 A t s t1 t2 f x).
Proof. exact (eq_refl (term120 A t s t1 t2 f x)). Qed.
Lemma lem7023930 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) : (term122 A t s t1 t2 f) = (term122 A t s t1 t2 f).
Proof. exact (fun_ext (fun x : A => @lem7023929 A t s t1 t2 f x)). Qed.
Lemma lem7023931 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7023932 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) : (term124 A t s t1 t2 f) = (term124 A t s t1 t2 f).
Proof. exact (MK_COMB (@lem7023931 A) (@lem7023930 A t s t1 t2 f)). Qed.
Lemma lem7023933 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> nat) : (term126 A t s t1 f) = (term126 A t s t1 f).
Proof. exact (fun_ext (fun t2 : A -> Prop => @lem7023932 A t s t1 t2 f)). Qed.
Lemma lem7023934 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7023935 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> nat) : (term128 A t s t1 f) = (term128 A t s t1 f).
Proof. exact (MK_COMB (@lem7023934 A) (@lem7023933 A t s t1 f)). Qed.
Lemma lem7023936 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term130 A t s f) = (term130 A t s f).
Proof. exact (fun_ext (fun t1 : A -> Prop => @lem7023935 A t s t1 f)). Qed.
Lemma lem7023937 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7023938 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term132 A t s f) = (term132 A t s f).
Proof. exact (MK_COMB (@lem7023937 A) (@lem7023936 A t s f)). Qed.
Lemma lem7023939 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7023940 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term269 A t s f) = (term269 A t s f).
Proof. exact (MK_COMB (@lem7023939) (@lem7023938 A t s f)). Qed.
Lemma lem7023941 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term271 A t s f) = (term271 A t s f).
Proof. exact (MK_COMB (@lem7023940 A t s f) (@lem7023898 A s f)). Qed.
Lemma lem7023950 {A : Type'} (t : A -> Prop) (s : type686 A) (t' : A -> Prop) : (term103 A t s t') = (term103 A t s t').
Proof. exact (eq_refl (term103 A t s t')). Qed.
Lemma lem7023951 {A : Type'} (t : A -> Prop) (s : type686 A) : (term105 A t s) = (term105 A t s).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem7023950 A t s t')). Qed.
Lemma lem7023952 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7023953 {A : Type'} (t : A -> Prop) (s : type686 A) : (term107 A t s) = (term107 A t s).
Proof. exact (MK_COMB (@lem7023952 A) (@lem7023951 A t s)). Qed.
Lemma lem7023954 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7023955 {A : Type'} (t : A -> Prop) (s : type686 A) : (term272 A t s) = (term272 A t s).
Proof. exact (MK_COMB (@lem7023954) (@lem7023953 A t s)). Qed.
Lemma lem7023956 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term273 A t s f) = (term273 A t s f).
Proof. exact (MK_COMB (@lem7023955 A t s) (@lem7023941 A t s f)). Qed.
Lemma lem7023957 {A : Type'} (s : type686 A) (f : A -> nat) : (term275 A s f) = (term275 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7023956 A t s f)). Qed.
Lemma lem7023958 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7023959 {A : Type'} (s : type686 A) (f : A -> nat) : (term277 A s f) = (term277 A s f).
Proof. exact (MK_COMB (@lem7023958 A) (@lem7023957 A s f)). Qed.
Lemma lem7023960 {A : Type'} (f : A -> nat) : (term279 A f) = (term279 A f).
Proof. exact (fun_ext (fun s : type686 A => @lem7023959 A s f)). Qed.
Lemma lem7023961 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem7023962 {A : Type'} (f : A -> nat) : (term281 A f) = (term281 A f).
Proof. exact (MK_COMB (@lem7023961 A) (@lem7023960 A f)). Qed.
Lemma lem7023963 {A : Type'} : (term283 A) = (term283 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem7023962 A f)). Qed.
Lemma lem7023964 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7023965 {A : Type'} : (term285 A) = (term285 A).
Proof. exact (MK_COMB (@lem7023964 A) (@lem7023963 A)). Qed.
Lemma lem7024060 {A : Type'} : (term284 A) = (term285 A).
Proof. exact (TRANS (@lem7023866 A) (@lem7023965 A)). Qed.
Lemma lem7024061 {A : Type'} : (term285 A) = (term284 A).
Proof. exact (SYM (@lem7024060 A)). Qed.
Lemma lem7024063 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term132 A t s f.
Proof. exact (h1). Qed.
Lemma lem7024066 (p : Prop) : p = (term260 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7024067 {A : Type'} (f : A -> nat) (x : A) : ((f x) = (NUMERAL 0)) = (term292 A f x).
Proof. exact (@lem7024066 ((f x) = (NUMERAL 0))). Qed.
Lemma lem7024068 {A : Type'} (f : A -> nat) (x : A) : (term292 A f x) = ((f x) = (NUMERAL 0)).
Proof. exact (SYM (@lem7024067 A f x)). Qed.
Lemma lem7024069 {A : Type'} (f : A -> nat) (x : A) (h1 : term293 A f x) : term293 A f x.
Proof. exact (h1). Qed.
Lemma lem7024129 {A : Type'} (t : A -> Prop) (t1 : A -> Prop) (s : type686 A) : (term294 A t t1 s) = (term295 A t t1 s).
Proof. exact (@lem17160 (t1 = t) (@IN (A -> Prop) t1 s)). Qed.
Lemma lem7024136 {A : Type'} (t : A -> Prop) (t2 : A -> Prop) (s : type686 A) : (term294 A t t2 s) = (term295 A t t2 s).
Proof. exact (@lem17160 (t2 = t) (@IN (A -> Prop) t2 s)). Qed.
Lemma lem7024139 {A : Type'} (t1 : A -> Prop) (t2 : A -> Prop) : (term296 A t1 t2) = (t1 = t2).
Proof. exact (@lem16933 (t1 = t2)). Qed.
Lemma lem7024146 {A : Type'} (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term297 A t1 x t2) = (term298 A t1 x t2).
Proof. exact (@lem17045 (@IN A x t1) (@IN A x t2)). Qed.
Lemma lem7024147 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7024148 {A : Type'} (t1 : A -> Prop) (t2 : A -> Prop) : (term299 A t1 t2) = (term187 A t1 t2).
Proof. exact (MK_COMB (@lem7024147) (@lem7024139 A t1 t2)). Qed.
Lemma lem7024149 {A : Type'} (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term300 A t1 x t2) = (term301 A t1 x t2).
Proof. exact (MK_COMB (@lem7024148 A t1 t2) (@lem7024146 A t1 x t2)). Qed.
Lemma lem7024150 {A : Type'} (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term302 A t1 x t2) = (term300 A t1 x t2).
Proof. exact (@lem17045 (term303 A t1 t2) (term304 A t1 x t2)). Qed.
Lemma lem7024151 {A : Type'} (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term302 A t1 x t2) = (term301 A t1 x t2).
Proof. exact (TRANS (@lem7024150 A t1 x t2) (@lem7024149 A t1 x t2)). Qed.
Lemma lem7024152 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7024153 {A : Type'} (t : A -> Prop) (t2 : A -> Prop) (s : type686 A) : (term305 A t t2 s) = (term306 A t t2 s).
Proof. exact (MK_COMB (@lem7024152) (@lem7024136 A t t2 s)). Qed.
Lemma lem7024154 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term307 A t s t1 x t2) = (term308 A t s t1 x t2).
Proof. exact (MK_COMB (@lem7024153 A t t2 s) (@lem7024151 A t1 x t2)). Qed.
Lemma lem7024155 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term309 A t s t1 x t2) = (term307 A t s t1 x t2).
Proof. exact (@lem17045 (term99 A t t2 s) (term112 A t1 x t2)). Qed.
Lemma lem7024156 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term309 A t s t1 x t2) = (term308 A t s t1 x t2).
Proof. exact (TRANS (@lem7024155 A t s t1 x t2) (@lem7024154 A t s t1 x t2)). Qed.
Lemma lem7024157 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7024158 {A : Type'} (t : A -> Prop) (t1 : A -> Prop) (s : type686 A) : (term305 A t t1 s) = (term306 A t t1 s).
Proof. exact (MK_COMB (@lem7024157) (@lem7024129 A t t1 s)). Qed.
Lemma lem7024159 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term310 A t s t1 x t2) = (term311 A t s t1 x t2).
Proof. exact (MK_COMB (@lem7024158 A t t1 s) (@lem7024156 A t s t1 x t2)). Qed.
Lemma lem7024160 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term312 A t s t1 x t2) = (term310 A t s t1 x t2).
Proof. exact (@lem17045 (term99 A t t1 s) (term114 A t s t1 x t2)). Qed.
Lemma lem7024161 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term312 A t s t1 x t2) = (term311 A t s t1 x t2).
Proof. exact (TRANS (@lem7024160 A t s t1 x t2) (@lem7024159 A t s t1 x t2)). Qed.
Lemma lem7024162 {A : Type'} (f : A -> nat) (x : A) : ((f x) = (NUMERAL 0)) = ((f x) = (NUMERAL 0)).
Proof. exact (eq_refl ((f x) = (NUMERAL 0))). Qed.
Lemma lem7024163 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7024164 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term313 A t s t1 x t2) = (term314 A t s t1 x t2).
Proof. exact (MK_COMB (@lem7024163) (@lem7024161 A t s t1 x t2)). Qed.
Lemma lem7024165 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) (x : A) : (term315 A t s t1 t2 f x) = (term316 A t s t1 t2 f x).
Proof. exact (MK_COMB (@lem7024164 A t s t1 x t2) (@lem7024162 A f x)). Qed.
Lemma lem7024166 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) (x : A) : (term120 A t s t1 t2 f x) = (term315 A t s t1 t2 f x).
Proof. exact (@lem17265 (term116 A t s t1 x t2) ((f x) = (NUMERAL 0))). Qed.
Lemma lem7024167 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) (x : A) : (term120 A t s t1 t2 f x) = (term316 A t s t1 t2 f x).
Proof. exact (TRANS (@lem7024166 A t s t1 t2 f x) (@lem7024165 A t s t1 t2 f x)). Qed.
Lemma lem7024168 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) : (term122 A t s t1 t2 f) = (term317 A t s t1 t2 f).
Proof. exact (fun_ext (fun x : A => @lem7024167 A t s t1 t2 f x)). Qed.
Lemma lem7024169 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7024170 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) : (term124 A t s t1 t2 f) = (term318 A t s t1 t2 f).
Proof. exact (MK_COMB (@lem7024169 A) (@lem7024168 A t s t1 t2 f)). Qed.
Lemma lem7024171 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> nat) : (term126 A t s t1 f) = (term319 A t s t1 f).
Proof. exact (fun_ext (fun t2 : A -> Prop => @lem7024170 A t s t1 t2 f)). Qed.
Lemma lem7024172 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7024173 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> nat) : (term128 A t s t1 f) = (term320 A t s t1 f).
Proof. exact (MK_COMB (@lem7024172 A) (@lem7024171 A t s t1 f)). Qed.
Lemma lem7024174 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term130 A t s f) = (term321 A t s f).
Proof. exact (fun_ext (fun t1 : A -> Prop => @lem7024173 A t s t1 f)). Qed.
Lemma lem7024175 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7024236 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term132 A t s f) = (term322 A t s f).
Proof. exact (MK_COMB (@lem7024175 A) (@lem7024174 A t s f)). Qed.
Lemma lem7024237 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term322 A t s f.
Proof. exact (EQ_MP (@lem7024236 A t s f) (@lem7024063 A t s f h1)). Qed.
Lemma lem7024259 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term323 A s t1 x t2) : term323 A s t1 x t2.
Proof. exact (h1). Qed.
Lemma lem7024265 {A : Type'} (f : A -> nat) (x : A) (h1 : term293 A f x) : term293 A f x.
Proof. exact (h1). Qed.
Lemma lem7024369 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) (x : A) : (term316 A t s t1 t2 f x) = (term316 A t s t1 t2 f x).
Proof. exact (eq_refl (term316 A t s t1 t2 f x)). Qed.
Lemma lem7024370 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) : (term317 A t s t1 t2 f) = (term317 A t s t1 t2 f).
Proof. exact (fun_ext (fun x : A => @lem7024369 A t s t1 t2 f x)). Qed.
Lemma lem7024371 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7024372 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) : (term318 A t s t1 t2 f) = (term318 A t s t1 t2 f).
Proof. exact (MK_COMB (@lem7024371 A) (@lem7024370 A t s t1 t2 f)). Qed.
Lemma lem7024373 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> nat) : (term319 A t s t1 f) = (term319 A t s t1 f).
Proof. exact (fun_ext (fun t2 : A -> Prop => @lem7024372 A t s t1 t2 f)). Qed.
Lemma lem7024374 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7024375 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> nat) : (term320 A t s t1 f) = (term320 A t s t1 f).
Proof. exact (MK_COMB (@lem7024374 A) (@lem7024373 A t s t1 f)). Qed.
Lemma lem7024376 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term321 A t s f) = (term321 A t s f).
Proof. exact (fun_ext (fun t1 : A -> Prop => @lem7024375 A t s t1 f)). Qed.
Lemma lem7024377 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7024378 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term322 A t s f) = (term322 A t s f).
Proof. exact (MK_COMB (@lem7024377 A) (@lem7024376 A t s f)). Qed.
Lemma lem7024379 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term322 A t s f.
Proof. exact (EQ_MP (@lem7024378 A t s f) (@lem7024237 A t s f h1)). Qed.
Lemma lem7024419 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term323 A s t1 x t2) : term323 A s t1 x t2.
Proof. exact (h1). Qed.
Lemma lem7024431 {A : Type'} (f : A -> nat) (x : A) (h1 : term293 A f x) : term293 A f x.
Proof. exact (h1). Qed.
Lemma lem7024432 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term323 A s t1 x t2) : term324 A s t1 x t2.
Proof. exact (proj2 (@lem7024419 A s t1 x t2 h1)). Qed.
Lemma lem7024434 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term323 A s t1 x t2) : term112 A t1 x t2.
Proof. exact (proj2 (@lem7024432 A s t1 x t2 h1)). Qed.
Lemma lem7024436 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term323 A s t1 x t2) : term304 A t1 x t2.
Proof. exact (proj2 (@lem7024434 A s t1 x t2 h1)). Qed.
Lemma lem7024464 {A : Type'} (f : A -> nat) (x : A) : ((f x) = (NUMERAL 0)) = ((f x) = (NUMERAL 0)).
Proof. exact (eq_refl ((f x) = (NUMERAL 0))). Qed.
Lemma lem7024493 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term308 A t s t1 x t2) = (term325 A t s t1 x t2).
Proof. exact (@lem19699 (term303 A t2 t) (term216 A t2 s) (term301 A t1 x t2)). Qed.
Lemma lem7024500 {A : Type'} (t : A -> Prop) (t1 : A -> Prop) (s : type686 A) : (term306 A t t1 s) = (term306 A t t1 s).
Proof. exact (eq_refl (term306 A t t1 s)). Qed.
Lemma lem7024501 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term311 A t s t1 x t2) = (term326 A t s t1 x t2).
Proof. exact (MK_COMB (@lem7024500 A t t1 s) (@lem7024493 A t s t1 x t2)). Qed.
Lemma lem7024502 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term326 A t s t1 x t2) = (term327 A t s t1 x t2).
Proof. exact (@lem19490 (term328 A t t1 x t2) (term295 A t t1 s) (term329 A s t1 x t2)). Qed.
Lemma lem7024509 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term330 A t s t1 x t2) = (term331 A t s t1 x t2).
Proof. exact (@lem19699 (term303 A t1 t) (term216 A t1 s) (term329 A s t1 x t2)). Qed.
Lemma lem7024516 {A : Type'} (s : type686 A) (t : A -> Prop) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term332 A s t t1 x t2) = (term333 A s t t1 x t2).
Proof. exact (@lem19699 (term303 A t1 t) (term216 A t1 s) (term328 A t t1 x t2)). Qed.
Lemma lem7024517 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7024518 {A : Type'} (s : type686 A) (t : A -> Prop) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term334 A s t t1 x t2) = (term335 A s t t1 x t2).
Proof. exact (MK_COMB (@lem7024517) (@lem7024516 A s t t1 x t2)). Qed.
Lemma lem7024519 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term327 A t s t1 x t2) = (term336 A t s t1 x t2).
Proof. exact (MK_COMB (@lem7024518 A s t t1 x t2) (@lem7024509 A t s t1 x t2)). Qed.
Lemma lem7024520 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term326 A t s t1 x t2) = (term336 A t s t1 x t2).
Proof. exact (TRANS (@lem7024502 A t s t1 x t2) (@lem7024519 A t s t1 x t2)). Qed.
Lemma lem7024521 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term311 A t s t1 x t2) = (term336 A t s t1 x t2).
Proof. exact (TRANS (@lem7024501 A t s t1 x t2) (@lem7024520 A t s t1 x t2)). Qed.
Lemma lem7024522 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7024523 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term314 A t s t1 x t2) = (term337 A t s t1 x t2).
Proof. exact (MK_COMB (@lem7024522) (@lem7024521 A t s t1 x t2)). Qed.
Lemma lem7024524 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) (x : A) : (term316 A t s t1 t2 f x) = (term338 A t s t1 t2 f x).
Proof. exact (MK_COMB (@lem7024523 A t s t1 x t2) (@lem7024464 A f x)). Qed.
Lemma lem7024525 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) (x : A) : (term338 A t s t1 t2 f x) = (term339 A t s t1 t2 f x).
Proof. exact (@lem19699 (term333 A s t t1 x t2) (term331 A t s t1 x t2) ((f x) = (NUMERAL 0))). Qed.
Lemma lem7024532 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) (x : A) : (term340 A t s t1 t2 f x) = (term341 A t s t1 t2 f x).
Proof. exact (@lem19699 (term342 A t s t1 x t2) (term343 A s t1 x t2) ((f x) = (NUMERAL 0))). Qed.
Lemma lem7024539 {A : Type'} (s : type686 A) (t : A -> Prop) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) (x : A) : (term344 A s t t1 t2 f x) = (term345 A s t t1 t2 f x).
Proof. exact (@lem19699 (term346 A t t1 x t2) (term347 A s t t1 x t2) ((f x) = (NUMERAL 0))). Qed.
Lemma lem7024540 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7024541 {A : Type'} (s : type686 A) (t : A -> Prop) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) (x : A) : (term348 A s t t1 t2 f x) = (term349 A s t t1 t2 f x).
Proof. exact (MK_COMB (@lem7024540) (@lem7024539 A s t t1 t2 f x)). Qed.
Lemma lem7024542 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) (x : A) : (term339 A t s t1 t2 f x) = (term350 A t s t1 t2 f x).
Proof. exact (MK_COMB (@lem7024541 A s t t1 t2 f x) (@lem7024532 A t s t1 t2 f x)). Qed.
Lemma lem7024543 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) (x : A) : (term338 A t s t1 t2 f x) = (term350 A t s t1 t2 f x).
Proof. exact (TRANS (@lem7024525 A t s t1 t2 f x) (@lem7024542 A t s t1 t2 f x)). Qed.
Lemma lem7024544 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) (x : A) : (term316 A t s t1 t2 f x) = (term350 A t s t1 t2 f x).
Proof. exact (TRANS (@lem7024524 A t s t1 t2 f x) (@lem7024543 A t s t1 t2 f x)). Qed.
Lemma lem7024545 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) : (term317 A t s t1 t2 f) = (term351 A t s t1 t2 f).
Proof. exact (fun_ext (fun x : A => @lem7024544 A t s t1 t2 f x)). Qed.
Lemma lem7024546 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7024547 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) : (term318 A t s t1 t2 f) = (term352 A t s t1 t2 f).
Proof. exact (MK_COMB (@lem7024546 A) (@lem7024545 A t s t1 t2 f)). Qed.
Lemma lem7024548 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> nat) : (term319 A t s t1 f) = (term353 A t s t1 f).
Proof. exact (fun_ext (fun t2 : A -> Prop => @lem7024547 A t s t1 t2 f)). Qed.
Lemma lem7024549 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7024550 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> nat) : (term320 A t s t1 f) = (term354 A t s t1 f).
Proof. exact (MK_COMB (@lem7024549 A) (@lem7024548 A t s t1 f)). Qed.
Lemma lem7024551 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term321 A t s f) = (term355 A t s f).
Proof. exact (fun_ext (fun t1 : A -> Prop => @lem7024550 A t s t1 f)). Qed.
Lemma lem7024552 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7024554 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term322 A t s f) = (term356 A t s f).
Proof. exact (MK_COMB (@lem7024552 A) (@lem7024551 A t s f)). Qed.
Lemma lem7024555 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term356 A t s f.
Proof. exact (EQ_MP (@lem7024554 A t s f) (@lem7024379 A t s f h1)). Qed.
Lemma lem7024559 {A : Type'} (f : A -> nat) (x : A) (h1 : term293 A f x) : term293 A f x.
Proof. exact (h1). Qed.
Lemma lem7024583 {A : Type'} (_93821 : A -> Prop) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term357 A t s f _93821.
Proof. exact (@lem7024555 A t s f h1 _93821). Qed.
Lemma lem7024584 {A : Type'} (t : A -> Prop) (s : type686 A) (_93821 : A -> Prop) (f : A -> nat) : (term357 A t s f _93821) = (term354 A t s _93821 f).
Proof. exact (eq_refl (term357 A t s f _93821)). Qed.
Lemma lem7024585 {A : Type'} (_93821 : A -> Prop) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term354 A t s _93821 f.
Proof. exact (EQ_MP (@lem7024584 A t s _93821 f) (@lem7024583 A _93821 t s f h1)). Qed.
Lemma lem7024586 {A : Type'} (_93821 : A -> Prop) (_93822 : A -> Prop) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term358 A t s _93821 f _93822.
Proof. exact (@lem7024585 A _93821 t s f h1 _93822). Qed.
Lemma lem7024587 {A : Type'} (t : A -> Prop) (s : type686 A) (_93821 : A -> Prop) (_93822 : A -> Prop) (f : A -> nat) : (term358 A t s _93821 f _93822) = (term352 A t s _93821 _93822 f).
Proof. exact (eq_refl (term358 A t s _93821 f _93822)). Qed.
Lemma lem7024588 {A : Type'} (_93821 : A -> Prop) (_93822 : A -> Prop) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term352 A t s _93821 _93822 f.
Proof. exact (EQ_MP (@lem7024587 A t s _93821 _93822 f) (@lem7024586 A _93821 _93822 t s f h1)). Qed.
Lemma lem7024589 {A : Type'} (_93821 : A -> Prop) (_93822 : A -> Prop) (_93823 : A) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term359 A t s _93821 _93822 f _93823.
Proof. exact (@lem7024588 A _93821 _93822 t s f h1 _93823). Qed.
Lemma lem7024590 {A : Type'} (t : A -> Prop) (s : type686 A) (_93821 : A -> Prop) (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : (term359 A t s _93821 _93822 f _93823) = (term350 A t s _93821 _93822 f _93823).
Proof. exact (eq_refl (term359 A t s _93821 _93822 f _93823)). Qed.
Lemma lem7024591 {A : Type'} (_93821 : A -> Prop) (_93822 : A -> Prop) (_93823 : A) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term350 A t s _93821 _93822 f _93823.
Proof. exact (EQ_MP (@lem7024590 A t s _93821 _93822 f _93823) (@lem7024589 A _93821 _93822 _93823 t s f h1)). Qed.
Lemma lem7024592 {A : Type'} (_93821 : A -> Prop) (_93822 : A -> Prop) (_93823 : A) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term341 A t s _93821 _93822 f _93823.
Proof. exact (proj2 (@lem7024591 A _93821 _93822 _93823 t s f h1)). Qed.
Lemma lem7024594 {A : Type'} (_93821 : A -> Prop) (_93822 : A -> Prop) (_93823 : A) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term360 A s _93821 _93822 f _93823.
Proof. exact (proj2 (@lem7024592 A _93821 _93822 _93823 t s f h1)). Qed.
Lemma lem7024601 {A : Type'} (f : A -> nat) (x : A) (h1 : term293 A f x) : term293 A f x.
Proof. exact (h1). Qed.
Lemma lem7024607 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term323 A s t1 x t2) : term303 A t1 t2.
Proof. exact (proj1 (@lem7024434 A s t1 x t2 h1)). Qed.
Lemma lem7024645 {A : Type'} (s : type686 A) (_93821 : A -> Prop) (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : (term360 A s _93821 _93822 f _93823) = (term361 A s _93821 _93822 f _93823).
Proof. exact (@lem7018663 (term216 A _93821 s) (term329 A s _93821 _93823 _93822) ((f _93823) = (NUMERAL 0))). Qed.
Lemma lem7024646 {A : Type'} (s : type686 A) (_93821 : A -> Prop) (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : (term362 A s _93821 _93822 f _93823) = (term363 A s _93821 _93822 f _93823).
Proof. exact (@lem7018663 (term216 A _93822 s) (term301 A _93821 _93823 _93822) ((f _93823) = (NUMERAL 0))). Qed.
Lemma lem7024647 {A : Type'} (_93821 : A -> Prop) (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : (term364 A _93821 _93822 f _93823) = (term365 A _93821 _93822 f _93823).
Proof. exact (@lem7018663 (_93821 = _93822) (term298 A _93821 _93823 _93822) ((f _93823) = (NUMERAL 0))). Qed.
Lemma lem7024654 {A : Type'} (_93821 : A -> Prop) (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : (term366 A _93821 _93822 f _93823) = (term367 A _93821 _93822 f _93823).
Proof. exact (@lem7018663 (term368 A _93823 _93821) (term368 A _93823 _93822) ((f _93823) = (NUMERAL 0))). Qed.
Lemma lem7024655 {A : Type'} (_93821 : A -> Prop) (_93822 : A -> Prop) : (term187 A _93821 _93822) = (term187 A _93821 _93822).
Proof. exact (eq_refl (term187 A _93821 _93822)). Qed.
Lemma lem7024658 {A : Type'} (_93821 : A -> Prop) (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : (term365 A _93821 _93822 f _93823) = (term369 A _93821 _93822 f _93823).
Proof. exact (MK_COMB (@lem7024655 A _93821 _93822) (@lem7024654 A _93821 _93822 f _93823)). Qed.
Lemma lem7024659 {A : Type'} (_93821 : A -> Prop) (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : (term364 A _93821 _93822 f _93823) = (term369 A _93821 _93822 f _93823).
Proof. exact (TRANS (@lem7024647 A _93821 _93822 f _93823) (@lem7024658 A _93821 _93822 f _93823)). Qed.
Lemma lem7024660 {A : Type'} (_93822 : A -> Prop) (s : type686 A) : (term370 A _93822 s) = (term370 A _93822 s).
Proof. exact (eq_refl (term370 A _93822 s)). Qed.
Lemma lem7024663 {A : Type'} (s : type686 A) (_93821 : A -> Prop) (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : (term363 A s _93821 _93822 f _93823) = (term371 A s _93821 _93822 f _93823).
Proof. exact (MK_COMB (@lem7024660 A _93822 s) (@lem7024659 A _93821 _93822 f _93823)). Qed.
Lemma lem7024664 {A : Type'} (s : type686 A) (_93821 : A -> Prop) (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : (term362 A s _93821 _93822 f _93823) = (term371 A s _93821 _93822 f _93823).
Proof. exact (TRANS (@lem7024646 A s _93821 _93822 f _93823) (@lem7024663 A s _93821 _93822 f _93823)). Qed.
Lemma lem7024665 {A : Type'} (_93821 : A -> Prop) (s : type686 A) : (term370 A _93821 s) = (term370 A _93821 s).
Proof. exact (eq_refl (term370 A _93821 s)). Qed.
Lemma lem7024668 {A : Type'} (s : type686 A) (_93821 : A -> Prop) (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : (term361 A s _93821 _93822 f _93823) = (term372 A s _93821 _93822 f _93823).
Proof. exact (MK_COMB (@lem7024665 A _93821 s) (@lem7024664 A s _93821 _93822 f _93823)). Qed.
Lemma lem7024670 {A : Type'} (s : type686 A) (_93821 : A -> Prop) (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : (term360 A s _93821 _93822 f _93823) = (term372 A s _93821 _93822 f _93823).
Proof. exact (TRANS (@lem7024645 A s _93821 _93822 f _93823) (@lem7024668 A s _93821 _93822 f _93823)). Qed.
Lemma lem7024671 {A : Type'} (_93821 : A -> Prop) (_93822 : A -> Prop) (_93823 : A) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term372 A s _93821 _93822 f _93823.
Proof. exact (EQ_MP (@lem7024670 A s _93821 _93822 f _93823) (@lem7024594 A _93821 _93822 _93823 t s f h1)). Qed.
Lemma lem7024819 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term323 A s t1 x t2) : @IN (A -> Prop) t1 s.
Proof. exact (proj1 (@lem7024419 A s t1 x t2 h1)). Qed.
Lemma lem7024820 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term323 A s t1 x t2) : term373 A t1 s.
Proof. exact (fun h0 : term216 A t1 s => @lem7024819 A s t1 x t2 h1). Qed.
Lemma lem7024822 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7024823 {A : Type'} (t1 : A -> Prop) (s : type686 A) : (term373 A t1 s) = (@IN (A -> Prop) t1 s).
Proof. exact (@lem7024822 (@IN (A -> Prop) t1 s)). Qed.
Lemma lem7024824 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term323 A s t1 x t2) : @IN (A -> Prop) t1 s.
Proof. exact (EQ_MP (@lem7024823 A t1 s) (@lem7024820 A s t1 x t2 h1)). Qed.
Lemma lem7024826 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term323 A s t1 x t2) : @IN (A -> Prop) t2 s.
Proof. exact (proj1 (@lem7024432 A s t1 x t2 h1)). Qed.
Lemma lem7024827 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term323 A s t1 x t2) : term373 A t2 s.
Proof. exact (fun h0 : term216 A t2 s => @lem7024826 A s t1 x t2 h1). Qed.
Lemma lem7024829 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7024830 {A : Type'} (t2 : A -> Prop) (s : type686 A) : (term373 A t2 s) = (@IN (A -> Prop) t2 s).
Proof. exact (@lem7024829 (@IN (A -> Prop) t2 s)). Qed.
Lemma lem7024831 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term323 A s t1 x t2) : @IN (A -> Prop) t2 s.
Proof. exact (EQ_MP (@lem7024830 A t2 s) (@lem7024827 A s t1 x t2 h1)). Qed.
Lemma lem7024833 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term323 A s t1 x t2) : @IN A x t1.
Proof. exact (proj1 (@lem7024436 A s t1 x t2 h1)). Qed.
Lemma lem7024834 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term323 A s t1 x t2) : term375 A x t1.
Proof. exact (fun h0 : term368 A x t1 => @lem7024833 A s t1 x t2 h1). Qed.
Lemma lem7024836 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7024837 {A : Type'} (x : A) (t1 : A -> Prop) : (term375 A x t1) = (@IN A x t1).
Proof. exact (@lem7024836 (@IN A x t1)). Qed.
Lemma lem7024838 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term323 A s t1 x t2) : @IN A x t1.
Proof. exact (EQ_MP (@lem7024837 A x t1) (@lem7024834 A s t1 x t2 h1)). Qed.
Lemma lem7024840 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term323 A s t1 x t2) : @IN A x t2.
Proof. exact (proj2 (@lem7024436 A s t1 x t2 h1)). Qed.
Lemma lem7024841 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term323 A s t1 x t2) : term375 A x t2.
Proof. exact (fun h0 : term368 A x t2 => @lem7024840 A s t1 x t2 h1). Qed.
Lemma lem7024843 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7024844 {A : Type'} (x : A) (t2 : A -> Prop) : (term375 A x t2) = (@IN A x t2).
Proof. exact (@lem7024843 (@IN A x t2)). Qed.
Lemma lem7024845 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term323 A s t1 x t2) : @IN A x t2.
Proof. exact (EQ_MP (@lem7024844 A x t2) (@lem7024841 A s t1 x t2 h1)). Qed.
Lemma lem7024847 {A : Type'} (f : A -> nat) (x : A) (h1 : term293 A f x) : term293 A f x.
Proof. exact (h1). Qed.
Lemma lem7024848 {A : Type'} (f : A -> nat) (x : A) (h1 : term293 A f x) : term376 A f x.
Proof. exact (fun h0 : (f x) = (NUMERAL 0) => @lem7024847 A f x h1). Qed.
Lemma lem7024850 (p : Prop) : (term377 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7024851 {A : Type'} (f : A -> nat) (x : A) : (term376 A f x) = (term293 A f x).
Proof. exact (@lem7024850 ((f x) = (NUMERAL 0))). Qed.
Lemma lem7024852 {A : Type'} (f : A -> nat) (x : A) (h1 : term293 A f x) : term293 A f x.
Proof. exact (EQ_MP (@lem7024851 A f x) (@lem7024848 A f x h1)). Qed.
Lemma lem7024868 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7024869 {A : Type'} (s : type686 A) (_93821 : A -> Prop) (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : (term371 A s _93821 _93822 f _93823) = (term378 A s _93821 _93822 f _93823).
Proof. exact (@lem7024868 (_93821 = _93822) (term216 A _93822 s) (term367 A _93821 _93822 f _93823)). Qed.
Lemma lem7024885 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7024886 {A : Type'} (_93821 : A -> Prop) (s : type686 A) (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : (term379 A s _93821 _93822 f _93823) = (term380 A _93821 s _93822 f _93823).
Proof. exact (@lem7024885 (term368 A _93823 _93821) (term216 A _93822 s) (term381 A _93822 f _93823)). Qed.
Lemma lem7024900 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7024901 {A : Type'} (_93822 : A -> Prop) (s : type686 A) (f : A -> nat) (_93823 : A) : (term382 A s _93822 f _93823) = (term383 A _93822 s f _93823).
Proof. exact (@lem7024900 (term368 A _93823 _93822) (term216 A _93822 s) ((f _93823) = (NUMERAL 0))). Qed.
Lemma lem7024915 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7024916 {A : Type'} (f : A -> nat) (_93823 : A) (_93822 : A -> Prop) (s : type686 A) : (term384 A _93822 s f _93823) = (term385 A f _93823 _93822 s).
Proof. exact (@lem7024915 ((f _93823) = (NUMERAL 0)) (term216 A _93822 s)). Qed.
Lemma lem7024924 {A : Type'} (_93823 : A) (_93822 : A -> Prop) : (term386 A _93823 _93822) = (term386 A _93823 _93822).
Proof. exact (eq_refl (term386 A _93823 _93822)). Qed.
Lemma lem7024925 {A : Type'} (f : A -> nat) (_93823 : A) (_93822 : A -> Prop) (s : type686 A) : (term383 A _93822 s f _93823) = (term387 A f _93823 _93822 s).
Proof. exact (MK_COMB (@lem7024924 A _93823 _93822) (@lem7024916 A f _93823 _93822 s)). Qed.
Lemma lem7024929 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7024930 {A : Type'} (f : A -> nat) (_93823 : A) (_93822 : A -> Prop) (s : type686 A) : (term387 A f _93823 _93822 s) = (term388 A f _93823 _93822 s).
Proof. exact (@lem7024929 ((f _93823) = (NUMERAL 0)) (term368 A _93823 _93822) (term216 A _93822 s)). Qed.
Lemma lem7024948 {A : Type'} (f : A -> nat) (_93823 : A) (_93822 : A -> Prop) (s : type686 A) : (term383 A _93822 s f _93823) = (term388 A f _93823 _93822 s).
Proof. exact (TRANS (@lem7024925 A f _93823 _93822 s) (@lem7024930 A f _93823 _93822 s)). Qed.
Lemma lem7024949 {A : Type'} (f : A -> nat) (_93823 : A) (_93822 : A -> Prop) (s : type686 A) : (term382 A s _93822 f _93823) = (term388 A f _93823 _93822 s).
Proof. exact (TRANS (@lem7024901 A _93822 s f _93823) (@lem7024948 A f _93823 _93822 s)). Qed.
Lemma lem7024950 {A : Type'} (_93823 : A) (_93821 : A -> Prop) : (term386 A _93823 _93821) = (term386 A _93823 _93821).
Proof. exact (eq_refl (term386 A _93823 _93821)). Qed.
Lemma lem7024951 {A : Type'} (_93821 : A -> Prop) (f : A -> nat) (_93823 : A) (_93822 : A -> Prop) (s : type686 A) : (term380 A _93821 s _93822 f _93823) = (term389 A _93821 f _93823 _93822 s).
Proof. exact (MK_COMB (@lem7024950 A _93823 _93821) (@lem7024949 A f _93823 _93822 s)). Qed.
Lemma lem7024955 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7024956 {A : Type'} (f : A -> nat) (_93821 : A -> Prop) (_93823 : A) (_93822 : A -> Prop) (s : type686 A) : (term389 A _93821 f _93823 _93822 s) = (term390 A f _93821 _93823 _93822 s).
Proof. exact (@lem7024955 ((f _93823) = (NUMERAL 0)) (term368 A _93823 _93821) (term391 A _93823 _93822 s)). Qed.
Lemma lem7024984 {A : Type'} (f : A -> nat) (_93821 : A -> Prop) (_93823 : A) (_93822 : A -> Prop) (s : type686 A) : (term380 A _93821 s _93822 f _93823) = (term390 A f _93821 _93823 _93822 s).
Proof. exact (TRANS (@lem7024951 A _93821 f _93823 _93822 s) (@lem7024956 A f _93821 _93823 _93822 s)). Qed.
Lemma lem7024985 {A : Type'} (f : A -> nat) (_93821 : A -> Prop) (_93823 : A) (_93822 : A -> Prop) (s : type686 A) : (term379 A s _93821 _93822 f _93823) = (term390 A f _93821 _93823 _93822 s).
Proof. exact (TRANS (@lem7024886 A _93821 s _93822 f _93823) (@lem7024984 A f _93821 _93823 _93822 s)). Qed.
Lemma lem7024986 {A : Type'} (_93821 : A -> Prop) (_93822 : A -> Prop) : (term187 A _93821 _93822) = (term187 A _93821 _93822).
Proof. exact (eq_refl (term187 A _93821 _93822)). Qed.
Lemma lem7024987 {A : Type'} (f : A -> nat) (_93821 : A -> Prop) (_93823 : A) (_93822 : A -> Prop) (s : type686 A) : (term378 A s _93821 _93822 f _93823) = (term392 A f _93821 _93823 _93822 s).
Proof. exact (MK_COMB (@lem7024986 A _93821 _93822) (@lem7024985 A f _93821 _93823 _93822 s)). Qed.
Lemma lem7024998 {A : Type'} (f : A -> nat) (_93821 : A -> Prop) (_93823 : A) (_93822 : A -> Prop) (s : type686 A) : (term371 A s _93821 _93822 f _93823) = (term392 A f _93821 _93823 _93822 s).
Proof. exact (TRANS (@lem7024869 A s _93821 _93822 f _93823) (@lem7024987 A f _93821 _93823 _93822 s)). Qed.
Lemma lem7024999 {A : Type'} (_93821 : A -> Prop) (s : type686 A) : (term370 A _93821 s) = (term370 A _93821 s).
Proof. exact (eq_refl (term370 A _93821 s)). Qed.
Lemma lem7025000 {A : Type'} (f : A -> nat) (_93821 : A -> Prop) (_93823 : A) (_93822 : A -> Prop) (s : type686 A) : (term372 A s _93821 _93822 f _93823) = (term393 A f _93821 _93823 _93822 s).
Proof. exact (MK_COMB (@lem7024999 A _93821 s) (@lem7024998 A f _93821 _93823 _93822 s)). Qed.
Lemma lem7025004 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7025005 {A : Type'} (f : A -> nat) (_93821 : A -> Prop) (_93823 : A) (_93822 : A -> Prop) (s : type686 A) : (term393 A f _93821 _93823 _93822 s) = (term394 A f _93821 _93823 _93822 s).
Proof. exact (@lem7025004 (_93821 = _93822) (term216 A _93821 s) (term390 A f _93821 _93823 _93822 s)). Qed.
Lemma lem7025021 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7025022 {A : Type'} (f : A -> nat) (_93821 : A -> Prop) (_93823 : A) (_93822 : A -> Prop) (s : type686 A) : (term395 A f _93821 _93823 _93822 s) = (term396 A f _93821 _93823 _93822 s).
Proof. exact (@lem7025021 ((f _93823) = (NUMERAL 0)) (term216 A _93821 s) (term397 A _93821 _93823 _93822 s)). Qed.
Lemma lem7025038 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7025039 {A : Type'} (_93821 : A -> Prop) (_93823 : A) (_93822 : A -> Prop) (s : type686 A) : (term398 A _93821 _93823 _93822 s) = (term399 A _93821 _93823 _93822 s).
Proof. exact (@lem7025038 (term368 A _93823 _93821) (term216 A _93821 s) (term391 A _93823 _93822 s)). Qed.
Lemma lem7025053 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7025054 {A : Type'} (_93823 : A) (_93821 : A -> Prop) (_93822 : A -> Prop) (s : type686 A) : (term400 A _93821 _93823 _93822 s) = (term401 A _93823 _93821 _93822 s).
Proof. exact (@lem7025053 (term368 A _93823 _93822) (term216 A _93821 s) (term216 A _93822 s)). Qed.
Lemma lem7025070 {A : Type'} (_93823 : A) (_93821 : A -> Prop) : (term386 A _93823 _93821) = (term386 A _93823 _93821).
Proof. exact (eq_refl (term386 A _93823 _93821)). Qed.
Lemma lem7025071 {A : Type'} (_93823 : A) (_93821 : A -> Prop) (_93822 : A -> Prop) (s : type686 A) : (term399 A _93821 _93823 _93822 s) = (term402 A _93823 _93821 _93822 s).
Proof. exact (MK_COMB (@lem7025070 A _93823 _93821) (@lem7025054 A _93823 _93821 _93822 s)). Qed.
Lemma lem7025082 {A : Type'} (_93823 : A) (_93821 : A -> Prop) (_93822 : A -> Prop) (s : type686 A) : (term398 A _93821 _93823 _93822 s) = (term402 A _93823 _93821 _93822 s).
Proof. exact (TRANS (@lem7025039 A _93821 _93823 _93822 s) (@lem7025071 A _93823 _93821 _93822 s)). Qed.
Lemma lem7025083 {A : Type'} (f : A -> nat) (_93823 : A) : (term403 A f _93823) = (term403 A f _93823).
Proof. exact (eq_refl (term403 A f _93823)). Qed.
Lemma lem7025084 {A : Type'} (f : A -> nat) (_93823 : A) (_93821 : A -> Prop) (_93822 : A -> Prop) (s : type686 A) : (term396 A f _93821 _93823 _93822 s) = (term404 A f _93823 _93821 _93822 s).
Proof. exact (MK_COMB (@lem7025083 A f _93823) (@lem7025082 A _93823 _93821 _93822 s)). Qed.
Lemma lem7025095 {A : Type'} (f : A -> nat) (_93823 : A) (_93821 : A -> Prop) (_93822 : A -> Prop) (s : type686 A) : (term395 A f _93821 _93823 _93822 s) = (term404 A f _93823 _93821 _93822 s).
Proof. exact (TRANS (@lem7025022 A f _93821 _93823 _93822 s) (@lem7025084 A f _93823 _93821 _93822 s)). Qed.
Lemma lem7025096 {A : Type'} (_93821 : A -> Prop) (_93822 : A -> Prop) : (term187 A _93821 _93822) = (term187 A _93821 _93822).
Proof. exact (eq_refl (term187 A _93821 _93822)). Qed.
Lemma lem7025097 {A : Type'} (f : A -> nat) (_93823 : A) (_93821 : A -> Prop) (_93822 : A -> Prop) (s : type686 A) : (term394 A f _93821 _93823 _93822 s) = (term405 A f _93823 _93821 _93822 s).
Proof. exact (MK_COMB (@lem7025096 A _93821 _93822) (@lem7025095 A f _93823 _93821 _93822 s)). Qed.
Lemma lem7025108 {A : Type'} (f : A -> nat) (_93823 : A) (_93821 : A -> Prop) (_93822 : A -> Prop) (s : type686 A) : (term393 A f _93821 _93823 _93822 s) = (term405 A f _93823 _93821 _93822 s).
Proof. exact (TRANS (@lem7025005 A f _93821 _93823 _93822 s) (@lem7025097 A f _93823 _93821 _93822 s)). Qed.
Lemma lem7025109 {A : Type'} (f : A -> nat) (_93823 : A) (_93821 : A -> Prop) (_93822 : A -> Prop) (s : type686 A) : (term372 A s _93821 _93822 f _93823) = (term405 A f _93823 _93821 _93822 s).
Proof. exact (TRANS (@lem7025000 A f _93821 _93823 _93822 s) (@lem7025108 A f _93823 _93821 _93822 s)). Qed.
Lemma lem7025110 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7025111 {A : Type'} (f : A -> nat) (_93823 : A) (_93821 : A -> Prop) (_93822 : A -> Prop) (s : type686 A) : (term406 A s _93821 _93822 f _93823) = (term407 A f _93823 _93821 _93822 s).
Proof. exact (MK_COMB (@lem7025110) (@lem7025109 A f _93823 _93821 _93822 s)). Qed.
Lemma lem7025137 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7025138 {A : Type'} (_93821 : A -> Prop) (s : type686 A) (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : (term379 A s _93821 _93822 f _93823) = (term380 A _93821 s _93822 f _93823).
Proof. exact (@lem7025137 (term368 A _93823 _93821) (term216 A _93822 s) (term381 A _93822 f _93823)). Qed.
Lemma lem7025152 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7025153 {A : Type'} (_93822 : A -> Prop) (s : type686 A) (f : A -> nat) (_93823 : A) : (term382 A s _93822 f _93823) = (term383 A _93822 s f _93823).
Proof. exact (@lem7025152 (term368 A _93823 _93822) (term216 A _93822 s) ((f _93823) = (NUMERAL 0))). Qed.
Lemma lem7025167 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7025168 {A : Type'} (f : A -> nat) (_93823 : A) (_93822 : A -> Prop) (s : type686 A) : (term384 A _93822 s f _93823) = (term385 A f _93823 _93822 s).
Proof. exact (@lem7025167 ((f _93823) = (NUMERAL 0)) (term216 A _93822 s)). Qed.
Lemma lem7025176 {A : Type'} (_93823 : A) (_93822 : A -> Prop) : (term386 A _93823 _93822) = (term386 A _93823 _93822).
Proof. exact (eq_refl (term386 A _93823 _93822)). Qed.
Lemma lem7025177 {A : Type'} (f : A -> nat) (_93823 : A) (_93822 : A -> Prop) (s : type686 A) : (term383 A _93822 s f _93823) = (term387 A f _93823 _93822 s).
Proof. exact (MK_COMB (@lem7025176 A _93823 _93822) (@lem7025168 A f _93823 _93822 s)). Qed.
Lemma lem7025181 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7025182 {A : Type'} (f : A -> nat) (_93823 : A) (_93822 : A -> Prop) (s : type686 A) : (term387 A f _93823 _93822 s) = (term388 A f _93823 _93822 s).
Proof. exact (@lem7025181 ((f _93823) = (NUMERAL 0)) (term368 A _93823 _93822) (term216 A _93822 s)). Qed.
Lemma lem7025200 {A : Type'} (f : A -> nat) (_93823 : A) (_93822 : A -> Prop) (s : type686 A) : (term383 A _93822 s f _93823) = (term388 A f _93823 _93822 s).
Proof. exact (TRANS (@lem7025177 A f _93823 _93822 s) (@lem7025182 A f _93823 _93822 s)). Qed.
Lemma lem7025201 {A : Type'} (f : A -> nat) (_93823 : A) (_93822 : A -> Prop) (s : type686 A) : (term382 A s _93822 f _93823) = (term388 A f _93823 _93822 s).
Proof. exact (TRANS (@lem7025153 A _93822 s f _93823) (@lem7025200 A f _93823 _93822 s)). Qed.
Lemma lem7025202 {A : Type'} (_93823 : A) (_93821 : A -> Prop) : (term386 A _93823 _93821) = (term386 A _93823 _93821).
Proof. exact (eq_refl (term386 A _93823 _93821)). Qed.
Lemma lem7025203 {A : Type'} (_93821 : A -> Prop) (f : A -> nat) (_93823 : A) (_93822 : A -> Prop) (s : type686 A) : (term380 A _93821 s _93822 f _93823) = (term389 A _93821 f _93823 _93822 s).
Proof. exact (MK_COMB (@lem7025202 A _93823 _93821) (@lem7025201 A f _93823 _93822 s)). Qed.
Lemma lem7025207 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7025208 {A : Type'} (f : A -> nat) (_93821 : A -> Prop) (_93823 : A) (_93822 : A -> Prop) (s : type686 A) : (term389 A _93821 f _93823 _93822 s) = (term390 A f _93821 _93823 _93822 s).
Proof. exact (@lem7025207 ((f _93823) = (NUMERAL 0)) (term368 A _93823 _93821) (term391 A _93823 _93822 s)). Qed.
Lemma lem7025236 {A : Type'} (f : A -> nat) (_93821 : A -> Prop) (_93823 : A) (_93822 : A -> Prop) (s : type686 A) : (term380 A _93821 s _93822 f _93823) = (term390 A f _93821 _93823 _93822 s).
Proof. exact (TRANS (@lem7025203 A _93821 f _93823 _93822 s) (@lem7025208 A f _93821 _93823 _93822 s)). Qed.
Lemma lem7025237 {A : Type'} (f : A -> nat) (_93821 : A -> Prop) (_93823 : A) (_93822 : A -> Prop) (s : type686 A) : (term379 A s _93821 _93822 f _93823) = (term390 A f _93821 _93823 _93822 s).
Proof. exact (TRANS (@lem7025138 A _93821 s _93822 f _93823) (@lem7025236 A f _93821 _93823 _93822 s)). Qed.
Lemma lem7025238 {A : Type'} (_93821 : A -> Prop) (s : type686 A) : (term370 A _93821 s) = (term370 A _93821 s).
Proof. exact (eq_refl (term370 A _93821 s)). Qed.
Lemma lem7025239 {A : Type'} (f : A -> nat) (_93821 : A -> Prop) (_93823 : A) (_93822 : A -> Prop) (s : type686 A) : (term408 A s _93821 _93822 f _93823) = (term395 A f _93821 _93823 _93822 s).
Proof. exact (MK_COMB (@lem7025238 A _93821 s) (@lem7025237 A f _93821 _93823 _93822 s)). Qed.
Lemma lem7025243 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7025244 {A : Type'} (f : A -> nat) (_93821 : A -> Prop) (_93823 : A) (_93822 : A -> Prop) (s : type686 A) : (term395 A f _93821 _93823 _93822 s) = (term396 A f _93821 _93823 _93822 s).
Proof. exact (@lem7025243 ((f _93823) = (NUMERAL 0)) (term216 A _93821 s) (term397 A _93821 _93823 _93822 s)). Qed.
Lemma lem7025260 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7025261 {A : Type'} (_93821 : A -> Prop) (_93823 : A) (_93822 : A -> Prop) (s : type686 A) : (term398 A _93821 _93823 _93822 s) = (term399 A _93821 _93823 _93822 s).
Proof. exact (@lem7025260 (term368 A _93823 _93821) (term216 A _93821 s) (term391 A _93823 _93822 s)). Qed.
Lemma lem7025275 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7025276 {A : Type'} (_93823 : A) (_93821 : A -> Prop) (_93822 : A -> Prop) (s : type686 A) : (term400 A _93821 _93823 _93822 s) = (term401 A _93823 _93821 _93822 s).
Proof. exact (@lem7025275 (term368 A _93823 _93822) (term216 A _93821 s) (term216 A _93822 s)). Qed.
Lemma lem7025292 {A : Type'} (_93823 : A) (_93821 : A -> Prop) : (term386 A _93823 _93821) = (term386 A _93823 _93821).
Proof. exact (eq_refl (term386 A _93823 _93821)). Qed.
Lemma lem7025293 {A : Type'} (_93823 : A) (_93821 : A -> Prop) (_93822 : A -> Prop) (s : type686 A) : (term399 A _93821 _93823 _93822 s) = (term402 A _93823 _93821 _93822 s).
Proof. exact (MK_COMB (@lem7025292 A _93823 _93821) (@lem7025276 A _93823 _93821 _93822 s)). Qed.
Lemma lem7025304 {A : Type'} (_93823 : A) (_93821 : A -> Prop) (_93822 : A -> Prop) (s : type686 A) : (term398 A _93821 _93823 _93822 s) = (term402 A _93823 _93821 _93822 s).
Proof. exact (TRANS (@lem7025261 A _93821 _93823 _93822 s) (@lem7025293 A _93823 _93821 _93822 s)). Qed.
Lemma lem7025305 {A : Type'} (f : A -> nat) (_93823 : A) : (term403 A f _93823) = (term403 A f _93823).
Proof. exact (eq_refl (term403 A f _93823)). Qed.
Lemma lem7025306 {A : Type'} (f : A -> nat) (_93823 : A) (_93821 : A -> Prop) (_93822 : A -> Prop) (s : type686 A) : (term396 A f _93821 _93823 _93822 s) = (term404 A f _93823 _93821 _93822 s).
Proof. exact (MK_COMB (@lem7025305 A f _93823) (@lem7025304 A _93823 _93821 _93822 s)). Qed.
Lemma lem7025317 {A : Type'} (f : A -> nat) (_93823 : A) (_93821 : A -> Prop) (_93822 : A -> Prop) (s : type686 A) : (term395 A f _93821 _93823 _93822 s) = (term404 A f _93823 _93821 _93822 s).
Proof. exact (TRANS (@lem7025244 A f _93821 _93823 _93822 s) (@lem7025306 A f _93823 _93821 _93822 s)). Qed.
Lemma lem7025318 {A : Type'} (f : A -> nat) (_93823 : A) (_93821 : A -> Prop) (_93822 : A -> Prop) (s : type686 A) : (term408 A s _93821 _93822 f _93823) = (term404 A f _93823 _93821 _93822 s).
Proof. exact (TRANS (@lem7025239 A f _93821 _93823 _93822 s) (@lem7025317 A f _93823 _93821 _93822 s)). Qed.
Lemma lem7025319 {A : Type'} (_93821 : A -> Prop) (_93822 : A -> Prop) : (term187 A _93821 _93822) = (term187 A _93821 _93822).
Proof. exact (eq_refl (term187 A _93821 _93822)). Qed.
Lemma lem7025320 {A : Type'} (f : A -> nat) (_93823 : A) (_93821 : A -> Prop) (_93822 : A -> Prop) (s : type686 A) : (term409 A s _93821 _93822 f _93823) = (term405 A f _93823 _93821 _93822 s).
Proof. exact (MK_COMB (@lem7025319 A _93821 _93822) (@lem7025318 A f _93823 _93821 _93822 s)). Qed.
Lemma lem7025331 {A : Type'} (f : A -> nat) (_93823 : A) (_93821 : A -> Prop) (_93822 : A -> Prop) (s : type686 A) : ((term372 A s _93821 _93822 f _93823) = (term409 A s _93821 _93822 f _93823)) = ((term405 A f _93823 _93821 _93822 s) = (term405 A f _93823 _93821 _93822 s)).
Proof. exact (MK_COMB (@lem7025111 A f _93823 _93821 _93822 s) (@lem7025320 A f _93823 _93821 _93822 s)). Qed.
Lemma lem7025333 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7025334 (x : Prop) : (x = x) = True.
Proof. exact (@lem7025333 Prop x). Qed.
Lemma lem7025335 {A : Type'} (f : A -> nat) (_93823 : A) (_93821 : A -> Prop) (_93822 : A -> Prop) (s : type686 A) : ((term405 A f _93823 _93821 _93822 s) = (term405 A f _93823 _93821 _93822 s)) = True.
Proof. exact (@lem7025334 (term405 A f _93823 _93821 _93822 s)). Qed.
Lemma lem7025336 {A : Type'} (s : type686 A) (_93821 : A -> Prop) (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : ((term372 A s _93821 _93822 f _93823) = (term409 A s _93821 _93822 f _93823)) = True.
Proof. exact (TRANS (@lem7025331 A f _93823 _93821 _93822 s) (@lem7025335 A f _93823 _93821 _93822 s)). Qed.
Lemma lem7025337 {A : Type'} (s : type686 A) (_93821 : A -> Prop) (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : True = ((term372 A s _93821 _93822 f _93823) = (term409 A s _93821 _93822 f _93823)).
Proof. exact (SYM (@lem7025336 A s _93821 _93822 f _93823)). Qed.
Lemma lem7025338 {A : Type'} (s : type686 A) (_93821 : A -> Prop) (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : (term372 A s _93821 _93822 f _93823) = (term409 A s _93821 _93822 f _93823).
Proof. exact (EQ_MP (@lem7025337 A s _93821 _93822 f _93823) (@lem0)). Qed.
Lemma lem7025339 {A : Type'} (_93821 : A -> Prop) (_93822 : A -> Prop) (_93823 : A) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term409 A s _93821 _93822 f _93823.
Proof. exact (EQ_MP (@lem7025338 A s _93821 _93822 f _93823) (@lem7024671 A _93821 _93822 _93823 t s f h1)). Qed.
Lemma lem7025341 (b : Prop) (a : Prop) : (a \/ b) = (term410 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7025342 {A : Type'} (s : type686 A) (f : A -> nat) (_93823 : A) (_93821 : A -> Prop) (_93822 : A -> Prop) : (term409 A s _93821 _93822 f _93823) = (term411 A s f _93823 _93821 _93822).
Proof. exact (@lem7025341 (term408 A s _93821 _93822 f _93823) (_93821 = _93822)). Qed.
Lemma lem7025344 (a : Prop) (b : Prop) : (term412 a b) = (term413 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7025345 {A : Type'} (s : type686 A) (_93821 : A -> Prop) (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : (term414 A s _93821 _93822 f _93823) = (term415 A s _93821 _93822 f _93823).
Proof. exact (@lem7025344 (term216 A _93821 s) (term379 A s _93821 _93822 f _93823)). Qed.
Lemma lem7025347 (a : Prop) : (term268 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7025348 {A : Type'} (_93821 : A -> Prop) (s : type686 A) : (term416 A _93821 s) = (@IN (A -> Prop) _93821 s).
Proof. exact (@lem7025347 (@IN (A -> Prop) _93821 s)). Qed.
Lemma lem7025349 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7025350 {A : Type'} (_93821 : A -> Prop) (s : type686 A) : (term417 A _93821 s) = (term418 A _93821 s).
Proof. exact (MK_COMB (@lem7025349) (@lem7025348 A _93821 s)). Qed.
Lemma lem7025352 (a : Prop) (b : Prop) : (term412 a b) = (term413 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7025353 {A : Type'} (s : type686 A) (_93821 : A -> Prop) (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : (term419 A s _93821 _93822 f _93823) = (term420 A s _93821 _93822 f _93823).
Proof. exact (@lem7025352 (term216 A _93822 s) (term367 A _93821 _93822 f _93823)). Qed.
Lemma lem7025355 (a : Prop) : (term268 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7025356 {A : Type'} (_93822 : A -> Prop) (s : type686 A) : (term416 A _93822 s) = (@IN (A -> Prop) _93822 s).
Proof. exact (@lem7025355 (@IN (A -> Prop) _93822 s)). Qed.
Lemma lem7025357 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7025358 {A : Type'} (_93822 : A -> Prop) (s : type686 A) : (term417 A _93822 s) = (term418 A _93822 s).
Proof. exact (MK_COMB (@lem7025357) (@lem7025356 A _93822 s)). Qed.
Lemma lem7025360 (a : Prop) (b : Prop) : (term412 a b) = (term413 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7025361 {A : Type'} (_93821 : A -> Prop) (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : (term421 A _93821 _93822 f _93823) = (term422 A _93821 _93822 f _93823).
Proof. exact (@lem7025360 (term368 A _93823 _93821) (term381 A _93822 f _93823)). Qed.
Lemma lem7025363 (a : Prop) : (term268 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7025364 {A : Type'} (_93823 : A) (_93821 : A -> Prop) : (term423 A _93823 _93821) = (@IN A _93823 _93821).
Proof. exact (@lem7025363 (@IN A _93823 _93821)). Qed.
Lemma lem7025365 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7025366 {A : Type'} (_93823 : A) (_93821 : A -> Prop) : (term424 A _93823 _93821) = (term425 A _93823 _93821).
Proof. exact (MK_COMB (@lem7025365) (@lem7025364 A _93823 _93821)). Qed.
Lemma lem7025368 (a : Prop) (b : Prop) : (term412 a b) = (term413 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7025369 {A : Type'} (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : (term426 A _93822 f _93823) = (term427 A _93822 f _93823).
Proof. exact (@lem7025368 (term368 A _93823 _93822) ((f _93823) = (NUMERAL 0))). Qed.
Lemma lem7025371 (a : Prop) : (term268 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7025372 {A : Type'} (_93823 : A) (_93822 : A -> Prop) : (term423 A _93823 _93822) = (@IN A _93823 _93822).
Proof. exact (@lem7025371 (@IN A _93823 _93822)). Qed.
Lemma lem7025373 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7025374 {A : Type'} (_93823 : A) (_93822 : A -> Prop) : (term424 A _93823 _93822) = (term425 A _93823 _93822).
Proof. exact (MK_COMB (@lem7025373) (@lem7025372 A _93823 _93822)). Qed.
Lemma lem7025375 {A : Type'} (f : A -> nat) (_93823 : A) : (term293 A f _93823) = (term293 A f _93823).
Proof. exact (eq_refl (term293 A f _93823)). Qed.
Lemma lem7025376 {A : Type'} (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : (term427 A _93822 f _93823) = (term428 A _93822 f _93823).
Proof. exact (MK_COMB (@lem7025374 A _93823 _93822) (@lem7025375 A f _93823)). Qed.
Lemma lem7025377 {A : Type'} (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : (term426 A _93822 f _93823) = (term428 A _93822 f _93823).
Proof. exact (TRANS (@lem7025369 A _93822 f _93823) (@lem7025376 A _93822 f _93823)). Qed.
Lemma lem7025378 {A : Type'} (_93821 : A -> Prop) (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : (term422 A _93821 _93822 f _93823) = (term429 A _93821 _93822 f _93823).
Proof. exact (MK_COMB (@lem7025366 A _93823 _93821) (@lem7025377 A _93822 f _93823)). Qed.
Lemma lem7025379 {A : Type'} (_93821 : A -> Prop) (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : (term421 A _93821 _93822 f _93823) = (term429 A _93821 _93822 f _93823).
Proof. exact (TRANS (@lem7025361 A _93821 _93822 f _93823) (@lem7025378 A _93821 _93822 f _93823)). Qed.
Lemma lem7025380 {A : Type'} (s : type686 A) (_93821 : A -> Prop) (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : (term420 A s _93821 _93822 f _93823) = (term430 A s _93821 _93822 f _93823).
Proof. exact (MK_COMB (@lem7025358 A _93822 s) (@lem7025379 A _93821 _93822 f _93823)). Qed.
Lemma lem7025381 {A : Type'} (s : type686 A) (_93821 : A -> Prop) (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : (term419 A s _93821 _93822 f _93823) = (term430 A s _93821 _93822 f _93823).
Proof. exact (TRANS (@lem7025353 A s _93821 _93822 f _93823) (@lem7025380 A s _93821 _93822 f _93823)). Qed.
Lemma lem7025382 {A : Type'} (s : type686 A) (_93821 : A -> Prop) (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : (term415 A s _93821 _93822 f _93823) = (term431 A s _93821 _93822 f _93823).
Proof. exact (MK_COMB (@lem7025350 A _93821 s) (@lem7025381 A s _93821 _93822 f _93823)). Qed.
Lemma lem7025383 {A : Type'} (s : type686 A) (_93821 : A -> Prop) (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : (term414 A s _93821 _93822 f _93823) = (term431 A s _93821 _93822 f _93823).
Proof. exact (TRANS (@lem7025345 A s _93821 _93822 f _93823) (@lem7025382 A s _93821 _93822 f _93823)). Qed.
Lemma lem7025384 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7025385 {A : Type'} (s : type686 A) (_93821 : A -> Prop) (_93822 : A -> Prop) (f : A -> nat) (_93823 : A) : (term432 A s _93821 _93822 f _93823) = (term433 A s _93821 _93822 f _93823).
Proof. exact (MK_COMB (@lem7025384) (@lem7025383 A s _93821 _93822 f _93823)). Qed.
Lemma lem7025386 {A : Type'} (_93821 : A -> Prop) (_93822 : A -> Prop) : (_93821 = _93822) = (_93821 = _93822).
Proof. exact (eq_refl (_93821 = _93822)). Qed.
Lemma lem7025387 {A : Type'} (s : type686 A) (f : A -> nat) (_93823 : A) (_93821 : A -> Prop) (_93822 : A -> Prop) : (term411 A s f _93823 _93821 _93822) = (term434 A s f _93823 _93821 _93822).
Proof. exact (MK_COMB (@lem7025385 A s _93821 _93822 f _93823) (@lem7025386 A _93821 _93822)). Qed.
Lemma lem7025388 {A : Type'} (s : type686 A) (f : A -> nat) (_93823 : A) (_93821 : A -> Prop) (_93822 : A -> Prop) : (term409 A s _93821 _93822 f _93823) = (term434 A s f _93823 _93821 _93822).
Proof. exact (TRANS (@lem7025342 A s f _93823 _93821 _93822) (@lem7025387 A s f _93823 _93821 _93822)). Qed.
Lemma lem7025390 {A : Type'} (f : A -> nat) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term293 A f x) (h2 : term323 A s t1 x t2) : term428 A t2 f x.
Proof. exact (conj (@lem7024845 A s t1 x t2 h2) (@lem7024852 A f x h1)). Qed.
Lemma lem7025391 {A : Type'} (f : A -> nat) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term293 A f x) (h2 : term323 A s t1 x t2) : term429 A t1 t2 f x.
Proof. exact (conj (@lem7024838 A s t1 x t2 h2) (@lem7025390 A f s t1 x t2 h1 h2)). Qed.
Lemma lem7025392 {A : Type'} (f : A -> nat) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term293 A f x) (h2 : term323 A s t1 x t2) : term430 A s t1 t2 f x.
Proof. exact (conj (@lem7024831 A s t1 x t2 h2) (@lem7025391 A f s t1 x t2 h1 h2)). Qed.
Lemma lem7025393 {A : Type'} (f : A -> nat) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term293 A f x) (h2 : term323 A s t1 x t2) : term431 A s t1 t2 f x.
Proof. exact (conj (@lem7024824 A s t1 x t2 h2) (@lem7025392 A f s t1 x t2 h1 h2)). Qed.
Lemma lem7025395 {A : Type'} (_93823 : A) (_93821 : A -> Prop) (_93822 : A -> Prop) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term434 A s f _93823 _93821 _93822.
Proof. exact (EQ_MP (@lem7025388 A s f _93823 _93821 _93822) (@lem7025339 A _93821 _93822 _93823 t s f h1)). Qed.
Lemma lem7025396 {A : Type'} (_93823 : A) (_93821 : A -> Prop) (_93822 : A -> Prop) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term434 A s f _93823 _93821 _93822.
Proof. exact (@lem7025395 A _93823 _93821 _93822 t s f h1). Qed.
Lemma lem7025397 {A : Type'} (x : A) (t1 : A -> Prop) (t2 : A -> Prop) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term434 A s f x t1 t2.
Proof. exact (@lem7025396 A x t1 t2 t s f h1). Qed.
Lemma lem7025400 {A : Type'} (t : A -> Prop) (f : A -> nat) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term323 A s t1 x t2) : t1 = t2.
Proof. exact (@lem7025397 A x t1 t2 t s f h1 (@lem7025393 A f s t1 x t2 h2 h3)). Qed.
Lemma lem7025401 {A : Type'} (t : A -> Prop) (f : A -> nat) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term323 A s t1 x t2) : term435 A t1 t2.
Proof. exact (fun h0 : term303 A t1 t2 => @lem7025400 A t f s t1 x t2 h1 h2 h3). Qed.
Lemma lem7025403 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7025404 {A : Type'} (t1 : A -> Prop) (t2 : A -> Prop) : (term435 A t1 t2) = (t1 = t2).
Proof. exact (@lem7025403 (t1 = t2)). Qed.
Lemma lem7025405 {A : Type'} (t : A -> Prop) (f : A -> nat) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term323 A s t1 x t2) : t1 = t2.
Proof. exact (EQ_MP (@lem7025404 A t1 t2) (@lem7025401 A t f s t1 x t2 h1 h2 h3)). Qed.
Lemma lem7025408 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7025410 {A : Type'} (t1 : A -> Prop) (t2 : A -> Prop) : (term303 A t1 t2) = (term436 A t1 t2).
Proof. exact (@lem7025408 (t1 = t2)). Qed.
Lemma lem7025413 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term323 A s t1 x t2) : term436 A t1 t2.
Proof. exact (EQ_MP (@lem7025410 A t1 t2) (@lem7024607 A s t1 x t2 h1)). Qed.
Lemma lem7025416 {A : Type'} (t : A -> Prop) (f : A -> nat) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term323 A s t1 x t2) : False.
Proof. exact (@lem7025413 A s t1 x t2 h3 (@lem7025405 A t f s t1 x t2 h1 h2 h3)). Qed.
Lemma lem7025417 {A : Type'} (t : A -> Prop) (f : A -> nat) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term323 A s t1 x t2) : term437.
Proof. exact (fun h0 : ~ False => @lem7025416 A t f s t1 x t2 h1 h2 h3). Qed.
Lemma lem7025419 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7025420 : term437 = False.
Proof. exact (@lem7025419 False). Qed.
Lemma lem7025421 {A : Type'} (t : A -> Prop) (f : A -> nat) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term323 A s t1 x t2) : False.
Proof. exact (EQ_MP (@lem7025420) (@lem7025417 A t f s t1 x t2 h1 h2 h3)). Qed.
Lemma lem7025422 {A : Type'} (t : A -> Prop) (f : A -> nat) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term323 A s t1 x t2) : (term293 A f x) = False.
Proof. exact (prop_ext (fun h4 : term293 A f x => @lem7025421 A t f s t1 x t2 h1 h2 h3) (fun h4 : False => @lem7024601 A f x h2)). Qed.
Lemma lem7025423 {A : Type'} (t : A -> Prop) (f : A -> nat) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term323 A s t1 x t2) : False.
Proof. exact (EQ_MP (@lem7025422 A t f s t1 x t2 h1 h2 h3) (@lem7024601 A f x h2)). Qed.
Lemma lem7025424 {A : Type'} (t : A -> Prop) (f : A -> nat) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term323 A s t1 x t2) : (term293 A f x) = False.
Proof. exact (prop_ext (fun h4 : term293 A f x => @lem7025423 A t f s t1 x t2 h1 h2 h3) (fun h4 : False => @lem7024559 A f x h2)). Qed.
Lemma lem7025425 {A : Type'} (t : A -> Prop) (f : A -> nat) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term323 A s t1 x t2) : False.
Proof. exact (EQ_MP (@lem7025424 A t f s t1 x t2 h1 h2 h3) (@lem7024559 A f x h2)). Qed.
Lemma lem7025426 {A : Type'} (t : A -> Prop) (f : A -> nat) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term323 A s t1 x t2) : (term293 A f x) = False.
Proof. exact (prop_ext (fun h4 : term293 A f x => @lem7025425 A t f s t1 x t2 h1 h2 h3) (fun h4 : False => @lem7024559 A f x h2)). Qed.
Lemma lem7025427 {A : Type'} (t : A -> Prop) (f : A -> nat) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term323 A s t1 x t2) : False.
Proof. exact (EQ_MP (@lem7025426 A t f s t1 x t2 h1 h2 h3) (@lem7024559 A f x h2)). Qed.
Lemma lem7025428 {A : Type'} (t : A -> Prop) (f : A -> nat) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term323 A s t1 x t2) : (term293 A f x) = False.
Proof. exact (prop_ext (fun h4 : term293 A f x => @lem7025427 A t f s t1 x t2 h1 h2 h3) (fun h4 : False => @lem7024431 A f x h2)). Qed.
Lemma lem7025429 {A : Type'} (t : A -> Prop) (f : A -> nat) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term323 A s t1 x t2) : False.
Proof. exact (EQ_MP (@lem7025428 A t f s t1 x t2 h1 h2 h3) (@lem7024431 A f x h2)). Qed.
Lemma lem7025430 {A : Type'} (t : A -> Prop) (f : A -> nat) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term323 A s t1 x t2) : (term323 A s t1 x t2) = False.
Proof. exact (prop_ext (fun h4 : term323 A s t1 x t2 => @lem7025429 A t f s t1 x t2 h1 h2 h3) (fun h4 : False => @lem7024419 A s t1 x t2 h3)). Qed.
Lemma lem7025431 {A : Type'} (t : A -> Prop) (f : A -> nat) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term323 A s t1 x t2) : False.
Proof. exact (EQ_MP (@lem7025430 A t f s t1 x t2 h1 h2 h3) (@lem7024419 A s t1 x t2 h3)). Qed.
Lemma lem7025432 {A : Type'} (t : A -> Prop) (f : A -> nat) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term323 A s t1 x t2) : (term293 A f x) = False.
Proof. exact (prop_ext (fun h4 : term293 A f x => @lem7025431 A t f s t1 x t2 h1 h2 h3) (fun h4 : False => @lem7024265 A f x h2)). Qed.
Lemma lem7025433 {A : Type'} (t : A -> Prop) (f : A -> nat) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term323 A s t1 x t2) : False.
Proof. exact (EQ_MP (@lem7025432 A t f s t1 x t2 h1 h2 h3) (@lem7024265 A f x h2)). Qed.
Lemma lem7025434 {A : Type'} (t : A -> Prop) (f : A -> nat) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term323 A s t1 x t2) : (term323 A s t1 x t2) = False.
Proof. exact (prop_ext (fun h4 : term323 A s t1 x t2 => @lem7025433 A t f s t1 x t2 h1 h2 h3) (fun h4 : False => @lem7024259 A s t1 x t2 h3)). Qed.
Lemma lem7025435 {A : Type'} (t : A -> Prop) (f : A -> nat) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term323 A s t1 x t2) : False.
Proof. exact (EQ_MP (@lem7025434 A t f s t1 x t2 h1 h2 h3) (@lem7024259 A s t1 x t2 h3)). Qed.
Lemma lem7025436 {A : Type'} (t : A -> Prop) (f : A -> nat) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term323 A s t1 x t2) : (term293 A f x) = False.
Proof. exact (prop_ext (fun h4 : term293 A f x => @lem7025435 A t f s t1 x t2 h1 h2 h3) (fun h4 : False => @lem7024069 A f x h2)). Qed.
Lemma lem7025437 {A : Type'} (t : A -> Prop) (f : A -> nat) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term323 A s t1 x t2) : False.
Proof. exact (EQ_MP (@lem7025436 A t f s t1 x t2 h1 h2 h3) (@lem7024069 A f x h2)). Qed.
Lemma lem7025438 {A : Type'} (t : A -> Prop) (f : A -> nat) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term132 A t s f) (h2 : term323 A s t1 x t2) : term292 A f x.
Proof. exact (fun h0 : term293 A f x => @lem7025437 A t f s t1 x t2 h1 h0 h2). Qed.
Lemma lem7025439 {A : Type'} (t : A -> Prop) (f : A -> nat) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term132 A t s f) (h2 : term323 A s t1 x t2) : (f x) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem7024068 A f x) (@lem7025438 A t f s t1 x t2 h1 h2)). Qed.
Lemma lem7025440 {A : Type'} (t1 : A -> Prop) (t2 : A -> Prop) (x : A) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term286 A s t1 t2 f x.
Proof. exact (fun h0 : term323 A s t1 x t2 => @lem7025439 A t f s t1 x t2 h1 h0). Qed.
Lemma lem7025445 {A : Type'} (t1 : A -> Prop) (t2 : A -> Prop) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term288 A s t1 t2 f.
Proof. exact (fun x : A => @lem7025440 A t1 t2 x t s f h1). Qed.
Lemma lem7025450 {A : Type'} (t1 : A -> Prop) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term290 A s t1 f.
Proof. exact (fun t2 : A -> Prop => @lem7025445 A t1 t2 t s f h1). Qed.
Lemma lem7025455 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term200 A s f.
Proof. exact (fun t1 : A -> Prop => @lem7025450 A t1 t s f h1). Qed.
Lemma lem7025456 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : term271 A t s f.
Proof. exact (fun h0 : term132 A t s f => @lem7025455 A t s f h0). Qed.
Lemma lem7025457 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : term273 A t s f.
Proof. exact (fun h0 : term107 A t s => @lem7025456 A t s f). Qed.
Lemma lem7025462 {A : Type'} (s : type686 A) (f : A -> nat) : term277 A s f.
Proof. exact (fun t : A -> Prop => @lem7025457 A t s f). Qed.
Lemma lem7025467 {A : Type'} (f : A -> nat) : term281 A f.
Proof. exact (fun s : type686 A => @lem7025462 A s f). Qed.
Lemma lem7025472 {A : Type'} : term285 A.
Proof. exact (fun f : A -> nat => @lem7025467 A f). Qed.
Lemma lem7025473 {A : Type'} : term284 A.
Proof. exact (EQ_MP (@lem7024061 A) (@lem7025472 A)). Qed.
Lemma lem7025474 {A : Type'} (f : A -> nat) : term438 A f.
Proof. exact (@lem7025473 A f). Qed.
Lemma lem7025475 {A : Type'} (f : A -> nat) : (term438 A f) = (term280 A f).
Proof. exact (eq_refl (term438 A f)). Qed.
Lemma lem7025476 {A : Type'} (f : A -> nat) : term280 A f.
Proof. exact (EQ_MP (@lem7025475 A f) (@lem7025474 A f)). Qed.
Lemma lem7025477 {A : Type'} (f : A -> nat) (s : type686 A) : term439 A f s.
Proof. exact (@lem7025476 A f s). Qed.
Lemma lem7025478 {A : Type'} (s : type686 A) (f : A -> nat) : (term439 A f s) = (term276 A s f).
Proof. exact (eq_refl (term439 A f s)). Qed.
Lemma lem7025479 {A : Type'} (s : type686 A) (f : A -> nat) : term276 A s f.
Proof. exact (EQ_MP (@lem7025478 A s f) (@lem7025477 A f s)). Qed.
Lemma lem7025480 {A : Type'} (s : type686 A) (f : A -> nat) (t : A -> Prop) : term440 A s f t.
Proof. exact (@lem7025479 A s f t). Qed.
Lemma lem7025481 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term440 A s f t) = (term263 A t s f).
Proof. exact (eq_refl (term440 A s f t)). Qed.
Lemma lem7025482 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : term263 A t s f.
Proof. exact (EQ_MP (@lem7025481 A t s f) (@lem7025480 A s f t)). Qed.
Lemma lem7025484 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : term263 A t s f.
Proof. exact (@lem7023754 A t s f (@lem7025482 A t s f)). Qed.
Lemma lem7025485 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : term270 A t s f.
Proof. exact (@lem7025484 A t s f (@lem7019138 A t s h1)). Qed.
Lemma lem7025486 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) : term261 A s f.
Proof. exact (@lem7025485 A f t s h2 (@lem7019137 A t s f h1)). Qed.
Lemma lem7025487 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) (h2 : term107 A t s) (h3 : term262 A s f) : False.
Proof. exact (@lem7025486 A f t s h1 h2 (@lem7023738 A s f h3)). Qed.
Lemma lem7025488 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) (h2 : term107 A t s) (h3 : term262 A s f) : (term262 A s f) = False.
Proof. exact (prop_ext (fun h4 : term262 A s f => @lem7025487 A t s f h1 h2 h3) (fun h4 : False => @lem7023738 A s f h3)). Qed.
Lemma lem7025489 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) (h2 : term107 A t s) (h3 : term262 A s f) : False.
Proof. exact (EQ_MP (@lem7025488 A t s f h1 h2 h3) (@lem7023738 A s f h3)). Qed.
Lemma lem7025490 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) : term261 A s f.
Proof. exact (fun h0 : term262 A s f => @lem7025489 A t s f h1 h2 h0). Qed.
Lemma lem7025491 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) : term200 A s f.
Proof. exact (EQ_MP (@lem7023737 A s f) (@lem7025490 A f t s h1 h2)). Qed.
Lemma lem7025492 {A : Type'} (s : type686 A) (f : A -> nat) (h1 : (term46 A s f) = (term47 A s f)) : (term46 A s f) = (term47 A s f).
Proof. exact (h1). Qed.
Lemma lem7025493 {A : Type'} (s : type686 A) (f : A -> nat) (h1 : (term46 A s f) = (term47 A s f)) : (term47 A s f) = (term46 A s f).
Proof. exact (SYM (@lem7025492 A s f h1)). Qed.
Lemma lem7025494 {A : Type'} (s : type686 A) (t : A -> Prop) (f : A -> nat) : (term441 A s t f) = (term441 A s t f).
Proof. exact (eq_refl (term441 A s t f)). Qed.
Lemma lem7025495 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : (term46 A s f) = (term47 A s f)) : (term442 A t s f) = (term443 A t s f).
Proof. exact (MK_COMB (@lem7025494 A s t f) (@lem7025493 A s f h1)). Qed.
Lemma lem7025496 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term443 A t s f) = (term444 A t s f).
Proof. exact (eq_refl (term443 A t s f)). Qed.
Lemma lem7025497 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term445 A t s f) = (term445 A t s f).
Proof. exact (eq_refl (term445 A t s f)). Qed.
Lemma lem7025498 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : ((term442 A t s f) = (term443 A t s f)) = ((term442 A t s f) = (term444 A t s f)).
Proof. exact (MK_COMB (@lem7025497 A t s f) (@lem7025496 A t s f)). Qed.
Lemma lem7025499 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term442 A t s f) = (term254 A t s f).
Proof. exact (eq_refl (term442 A t s f)). Qed.
Lemma lem7025500 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7025501 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term445 A t s f) = (term446 A t s f).
Proof. exact (MK_COMB (@lem7025500) (@lem7025499 A t s f)). Qed.
Lemma lem7025502 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term444 A t s f) = (term444 A t s f).
Proof. exact (eq_refl (term444 A t s f)). Qed.
Lemma lem7025503 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : ((term442 A t s f) = (term444 A t s f)) = ((term254 A t s f) = (term444 A t s f)).
Proof. exact (MK_COMB (@lem7025501 A t s f) (@lem7025502 A t s f)). Qed.
Lemma lem7025504 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : ((term442 A t s f) = (term443 A t s f)) = ((term254 A t s f) = (term444 A t s f)).
Proof. exact (TRANS (@lem7025498 A t s f) (@lem7025503 A t s f)). Qed.
Lemma lem7025505 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : (term46 A s f) = (term47 A s f)) : (term254 A t s f) = (term444 A t s f).
Proof. exact (EQ_MP (@lem7025504 A t s f) (@lem7025495 A t s f h1)). Qed.
Lemma lem7025506 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : (term46 A s f) = (term47 A s f)) : (term444 A t s f) = (term254 A t s f).
Proof. exact (SYM (@lem7025505 A t s f h1)). Qed.
Lemma lem7025520 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : term107 A t s.
Proof. exact (h1). Qed.
Lemma lem7025534 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term132 A t s f.
Proof. exact (h1). Qed.
Lemma lem7025535 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term63 A t s) : term63 A t s.
Proof. exact (h1). Qed.
Lemma lem7025536 {A : Type'} (s : type686 A) (h1 : @FINITE (A -> Prop) s) : @FINITE (A -> Prop) s.
Proof. exact (h1). Qed.
Lemma lem7025537 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term216 A t s) : term216 A t s.
Proof. exact (h1). Qed.
Lemma lem7025539 {_129614 : Type'} (s : _129614 -> Prop) (t : _129614 -> Prop) (f : _129614 -> nat) : term13 _129614 s t f.
Proof. exact (EQ_MP (@lem7018652 _129614 s t f) (@lem7018651 _129614 s t f)). Qed.
Lemma lem7025540 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : term13 A s t f.
Proof. exact (@lem7025539 A s t f). Qed.
Lemma lem7025541 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : term447 A t s f.
Proof. exact (@lem7025540 A t (@UNIONS A s) f). Qed.
Lemma lem7025542 {A : Type'} (s : type686 A) : term448 A s.
Proof. exact (@lem3205091 A s). Qed.
Lemma lem7025543 {A : Type'} (s : type686 A) : (term448 A s) = (term449 A s).
Proof. exact (eq_refl (term448 A s)). Qed.
Lemma lem7025544 {A : Type'} (s : type686 A) : term449 A s.
Proof. exact (EQ_MP (@lem7025543 A s) (@lem7025542 A s)). Qed.
Lemma lem7025545 {A : Type'} (s : type686 A) (x : A) : term450 A s x.
Proof. exact (@lem7025544 A s x). Qed.
Lemma lem7025546 {A : Type'} (s : type686 A) (x : A) : (term450 A s x) = ((term451 A x s) = (term452 A s x)).
Proof. exact (eq_refl (term450 A s x)). Qed.
Lemma lem7025548 {A : Type'} (s : A -> Prop) : term453 A s.
Proof. exact (@lem3205222 A s). Qed.
Lemma lem7025549 {A : Type'} (s : A -> Prop) : (term453 A s) = (term454 A s).
Proof. exact (eq_refl (term453 A s)). Qed.
Lemma lem7025550 {A : Type'} (s : A -> Prop) : term454 A s.
Proof. exact (EQ_MP (@lem7025549 A s) (@lem7025548 A s)). Qed.
Lemma lem7025551 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term455 A s t.
Proof. exact (@lem7025550 A s t). Qed.
Lemma lem7025552 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term455 A s t) = (term456 A s t).
Proof. exact (eq_refl (term455 A s t)). Qed.
Lemma lem7025553 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term456 A s t.
Proof. exact (EQ_MP (@lem7025552 A s t) (@lem7025551 A s t)). Qed.
Lemma lem7025554 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term457 A s t x.
Proof. exact (@lem7025553 A s t x). Qed.
Lemma lem7025555 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term457 A s t x) = ((term458 A x s t) = (term304 A s x t)).
Proof. exact (eq_refl (term457 A s t x)). Qed.
Lemma lem7025557 {A : Type'} (s : type686 A) : term459 A s.
Proof. exact (@lem4605902 A s). Qed.
Lemma lem7025558 {A : Type'} (s : type686 A) : (term459 A s) = ((term460 A s) = (term461 A s)).
Proof. exact (eq_refl (term459 A s)). Qed.
Lemma lem7025560 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : term164 A t s t'.
Proof. exact (@lem7025520 A t s h1 t'). Qed.
Lemma lem7025561 {A : Type'} (t : A -> Prop) (s : type686 A) (t' : A -> Prop) : (term164 A t s t') = (term103 A t s t').
Proof. exact (eq_refl (term164 A t s t')). Qed.
Lemma lem7025562 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : term103 A t s t'.
Proof. exact (EQ_MP (@lem7025561 A t s t') (@lem7025560 A t' t s h1)). Qed.
Lemma lem7025563 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (s : type686 A) (h1 : term99 A t t' s) : term99 A t t' s.
Proof. exact (h1). Qed.
Lemma lem7025564 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (s : type686 A) (h1 : term107 A t s) (h2 : term99 A t t' s) : @FINITE A t'.
Proof. exact (@lem7025562 A t' t s h1 (@lem7025563 A t t' s h2)). Qed.
Lemma lem7025565 {A : Type'} (t' : A -> Prop) : (@FINITE A t') = ((@FINITE A t') = True).
Proof. exact (@lem7 (@FINITE A t')). Qed.
Lemma lem7025566 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (s : type686 A) (h1 : term107 A t s) (h2 : term99 A t t' s) : (@FINITE A t') = True.
Proof. exact (EQ_MP (@lem7025565 A t') (@lem7025564 A t t' s h1 h2)). Qed.
Lemma lem7025640 {A : Type'} (t : A -> Prop) (s : type686 A) : term217 A t s.
Proof. exact (@lem82 (@IN (A -> Prop) t s)). Qed.
Lemma lem7025642 {A : Type'} (s : type686 A) : (@FINITE (A -> Prop) s) = ((@FINITE (A -> Prop) s) = True).
Proof. exact (@lem7 (@FINITE (A -> Prop) s)). Qed.
Lemma lem7025647 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : term186 A t s t'.
Proof. exact (fun h0 : term99 A t t' s => @lem7025566 A t t' s h1 h0). Qed.
Lemma lem7025648 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : term186 A t s t'.
Proof. exact (@lem7025647 A t' t s h1). Qed.
Lemma lem7025649 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : term462 A s t.
Proof. exact (@lem7025648 A t t s h1). Qed.
Lemma lem7025653 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7025654 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem7025653 (A -> Prop) x). Qed.
Lemma lem7025655 {A : Type'} (t : A -> Prop) : (t = t) = True.
Proof. exact (@lem7025654 A t). Qed.
Lemma lem7025656 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7025657 {A : Type'} (t : A -> Prop) : (term463 A t) = (or True).
Proof. exact (MK_COMB (@lem7025656) (@lem7025655 A t)). Qed.
Lemma lem7025659 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term216 A t s) : (@IN (A -> Prop) t s) = False.
Proof. exact (@lem7025640 A t s (@lem7025537 A t s h1)). Qed.
Lemma lem7025660 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term216 A t s) : (term464 A t s) = (True \/ False).
Proof. exact (MK_COMB (@lem7025657 A t) (@lem7025659 A t s h1)). Qed.
Lemma lem7025662 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem7025663 : (True \/ False) = True.
Proof. exact (@lem7025662 False). Qed.
Lemma lem7025664 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term216 A t s) : (term464 A t s) = True.
Proof. exact (TRANS (@lem7025660 A t s h1) (@lem7025663)). Qed.
Lemma lem7025665 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term216 A t s) : True = (term464 A t s).
Proof. exact (SYM (@lem7025664 A t s h1)). Qed.
Lemma lem7025666 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term216 A t s) : term464 A t s.
Proof. exact (EQ_MP (@lem7025665 A t s h1) (@lem0)). Qed.
Lemma lem7025667 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) (h2 : term216 A t s) : (@FINITE A t) = True.
Proof. exact (@lem7025649 A t s h1 (@lem7025666 A t s h2)). Qed.
Lemma lem7025668 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7025669 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) (h2 : term216 A t s) : (term465 A t) = (and True).
Proof. exact (MK_COMB (@lem7025668) (@lem7025667 A t s h1 h2)). Qed.
Lemma lem7025673 {A : Type'} (s : type686 A) : (term460 A s) = (term461 A s).
Proof. exact (EQ_MP (@lem7025558 A s) (@lem7025557 A s)). Qed.
Lemma lem7025674 {A : Type'} (s : type686 A) : (term460 A s) = (term461 A s).
Proof. exact (@lem7025673 A s). Qed.
Lemma lem7025678 {A : Type'} (s : type686 A) (h1 : @FINITE (A -> Prop) s) : (@FINITE (A -> Prop) s) = True.
Proof. exact (EQ_MP (@lem7025642 A s) (@lem7025536 A s h1)). Qed.
Lemma lem7025679 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7025680 {A : Type'} (s : type686 A) (h1 : @FINITE (A -> Prop) s) : (term466 A s) = (and True).
Proof. exact (MK_COMB (@lem7025679) (@lem7025678 A s h1)). Qed.
Lemma lem7025740 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term165 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7025741 (p : Prop) (q : Prop) (p' : Prop) : term166 p q p'.
Proof. exact (fun q' : Prop => @lem7025740 p q p' q'). Qed.
Lemma lem7025742 (p : Prop) (q : Prop) : term167 p q.
Proof. exact (fun p' : Prop => @lem7025741 p q p'). Qed.
Lemma lem7025743 {A : Type'} (s : type686 A) (_93844 : A -> Prop) : term179 A s _93844.
Proof. exact (@lem7025742 (@IN (A -> Prop) _93844 s) (@FINITE A _93844)). Qed.
Lemma lem7025744 {A : Type'} (s : type686 A) (_93844 : A -> Prop) (p' : Prop) : term180 A s _93844 p'.
Proof. exact (@lem7025743 A s _93844 p'). Qed.
Lemma lem7025745 {A : Type'} (s : type686 A) (_93844 : A -> Prop) (p' : Prop) : (term180 A s _93844 p') = (term181 A s _93844 p').
Proof. exact (eq_refl (term180 A s _93844 p')). Qed.
Lemma lem7025746 {A : Type'} (s : type686 A) (_93844 : A -> Prop) (p' : Prop) : term181 A s _93844 p'.
Proof. exact (EQ_MP (@lem7025745 A s _93844 p') (@lem7025744 A s _93844 p')). Qed.
Lemma lem7025747 {A : Type'} (s : type686 A) (_93844 : A -> Prop) (p' : Prop) (q' : Prop) : term182 A s _93844 p' q'.
Proof. exact (@lem7025746 A s _93844 p' q'). Qed.
Lemma lem7025748 {A : Type'} (s : type686 A) (_93844 : A -> Prop) (p' : Prop) (q' : Prop) : (term182 A s _93844 p' q') = (term183 A s _93844 p' q').
Proof. exact (eq_refl (term182 A s _93844 p' q')). Qed.
Lemma lem7025749 {A : Type'} (s : type686 A) (_93844 : A -> Prop) (p' : Prop) (q' : Prop) : term183 A s _93844 p' q'.
Proof. exact (EQ_MP (@lem7025748 A s _93844 p' q') (@lem7025747 A s _93844 p' q')). Qed.
Lemma lem7025750 {A : Type'} (_93844 : A -> Prop) (s : type686 A) : (@IN (A -> Prop) _93844 s) = (@IN (A -> Prop) _93844 s).
Proof. exact (eq_refl (@IN (A -> Prop) _93844 s)). Qed.
Lemma lem7025751 {A : Type'} (_93844 : A -> Prop) (s : type686 A) (q' : Prop) : term184 A _93844 s q'.
Proof. exact (@lem7025749 A s _93844 (@IN (A -> Prop) _93844 s) q'). Qed.
Lemma lem7025752 {A : Type'} (_93844 : A -> Prop) (s : type686 A) (q' : Prop) : term185 A _93844 s q'.
Proof. exact (@lem7025751 A _93844 s q' (@lem7025750 A _93844 s)). Qed.
Lemma lem7025753 {A : Type'} (_93844 : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) _93844 s) : @IN (A -> Prop) _93844 s.
Proof. exact (h1). Qed.
Lemma lem7025754 {A : Type'} (_93844 : A -> Prop) (s : type686 A) : (@IN (A -> Prop) _93844 s) = ((@IN (A -> Prop) _93844 s) = True).
Proof. exact (@lem7 (@IN (A -> Prop) _93844 s)). Qed.
Lemma lem7025757 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : term186 A t s t'.
Proof. exact (fun h0 : term99 A t t' s => @lem7025566 A t t' s h1 h0). Qed.
Lemma lem7025758 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : term186 A t s t'.
Proof. exact (@lem7025757 A t' t s h1). Qed.
Lemma lem7025759 {A : Type'} (_93844 : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : term186 A t s _93844.
Proof. exact (@lem7025758 A _93844 t s h1). Qed.
Lemma lem7025765 {A : Type'} (_93844 : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) _93844 s) : (@IN (A -> Prop) _93844 s) = True.
Proof. exact (EQ_MP (@lem7025754 A _93844 s) (@lem7025753 A _93844 s h1)). Qed.
Lemma lem7025766 {A : Type'} (_93844 : A -> Prop) (t : A -> Prop) : (term187 A _93844 t) = (term187 A _93844 t).
Proof. exact (eq_refl (term187 A _93844 t)). Qed.
Lemma lem7025767 {A : Type'} (t : A -> Prop) (_93844 : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) _93844 s) : (term99 A t _93844 s) = (term188 A _93844 t).
Proof. exact (MK_COMB (@lem7025766 A _93844 t) (@lem7025765 A _93844 s h1)). Qed.
Lemma lem7025769 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem7025770 {A : Type'} (_93844 : A -> Prop) (t : A -> Prop) : (term188 A _93844 t) = True.
Proof. exact (@lem7025769 (_93844 = t)). Qed.
Lemma lem7025771 {A : Type'} (t : A -> Prop) (_93844 : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) _93844 s) : (term99 A t _93844 s) = True.
Proof. exact (TRANS (@lem7025767 A t _93844 s h1) (@lem7025770 A _93844 t)). Qed.
Lemma lem7025772 {A : Type'} (t : A -> Prop) (_93844 : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) _93844 s) : True = (term99 A t _93844 s).
Proof. exact (SYM (@lem7025771 A t _93844 s h1)). Qed.
Lemma lem7025773 {A : Type'} (t : A -> Prop) (_93844 : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) _93844 s) : term99 A t _93844 s.
Proof. exact (EQ_MP (@lem7025772 A t _93844 s h1) (@lem0)). Qed.
Lemma lem7025774 {A : Type'} (t : A -> Prop) (_93844 : A -> Prop) (s : type686 A) (h1 : term107 A t s) (h2 : @IN (A -> Prop) _93844 s) : (@FINITE A _93844) = True.
Proof. exact (@lem7025759 A _93844 t s h1 (@lem7025773 A t _93844 s h2)). Qed.
Lemma lem7025775 {A : Type'} (_93844 : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : term189 A s _93844.
Proof. exact (fun h0 : @IN (A -> Prop) _93844 s => @lem7025774 A t _93844 s h1 h0). Qed.
Lemma lem7025776 {A : Type'} (_93844 : A -> Prop) (s : type686 A) : term190 A _93844 s.
Proof. exact (@lem7025752 A _93844 s True). Qed.
Lemma lem7025777 {A : Type'} (_93844 : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : (term191 A s _93844) = (term192 A _93844 s).
Proof. exact (@lem7025776 A _93844 s (@lem7025775 A _93844 t s h1)). Qed.
Lemma lem7025779 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7025780 {A : Type'} (_93844 : A -> Prop) (s : type686 A) : (term192 A _93844 s) = True.
Proof. exact (@lem7025779 (@IN (A -> Prop) _93844 s)). Qed.
Lemma lem7025781 {A : Type'} (_93844 : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : (term191 A s _93844) = True.
Proof. exact (TRANS (@lem7025777 A _93844 t s h1) (@lem7025780 A _93844 s)). Qed.
Lemma lem7025784 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : (term193 A s) = (term194 A).
Proof. exact (fun_ext (fun _93844 : A -> Prop => @lem7025781 A _93844 t s h1)). Qed.
Lemma lem7025785 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7025786 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : (term195 A s) = (term196 A).
Proof. exact (MK_COMB (@lem7025785 A) (@lem7025784 A t s h1)). Qed.
Lemma lem7025788 {A : Type'} (t : Prop) : (term197 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7025789 {A : Type'} (t : Prop) : (term198 A t) = t.
Proof. exact (@lem7025788 (A -> Prop) t). Qed.
Lemma lem7025790 {A : Type'} : (term196 A) = True.
Proof. exact (@lem7025789 A True). Qed.
Lemma lem7025791 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : (term195 A s) = True.
Proof. exact (TRANS (@lem7025786 A t s h1) (@lem7025790 A)). Qed.
Lemma lem7025792 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) (h2 : @FINITE (A -> Prop) s) : (term461 A s) = (True /\ True).
Proof. exact (MK_COMB (@lem7025680 A s h2) (@lem7025791 A t s h1)). Qed.
Lemma lem7025794 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7025795 : (True /\ True) = True.
Proof. exact (@lem7025794 True). Qed.
Lemma lem7025796 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) (h2 : @FINITE (A -> Prop) s) : (term461 A s) = True.
Proof. exact (TRANS (@lem7025792 A t s h1 h2) (@lem7025795)). Qed.
Lemma lem7025797 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) (h2 : @FINITE (A -> Prop) s) : (term460 A s) = True.
Proof. exact (TRANS (@lem7025674 A s) (@lem7025796 A t s h1 h2)). Qed.
Lemma lem7025798 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7025799 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) (h2 : @FINITE (A -> Prop) s) : (term467 A s) = (and True).
Proof. exact (MK_COMB (@lem7025798) (@lem7025797 A t s h1 h2)). Qed.
Lemma lem7025807 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term165 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7025808 (p : Prop) (q : Prop) (p' : Prop) : term166 p q p'.
Proof. exact (fun q' : Prop => @lem7025807 p q p' q'). Qed.
Lemma lem7025809 (p : Prop) (q : Prop) : term167 p q.
Proof. exact (fun p' : Prop => @lem7025808 p q p'). Qed.
Lemma lem7025810 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (x : A) : term468 A t s f x.
Proof. exact (@lem7025809 (term469 A x t s) ((f x) = (NUMERAL 0))). Qed.
Lemma lem7025811 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (x : A) (p' : Prop) : term470 A t s f x p'.
Proof. exact (@lem7025810 A t s f x p'). Qed.
Lemma lem7025812 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (x : A) (p' : Prop) : (term470 A t s f x p') = (term471 A t s f x p').
Proof. exact (eq_refl (term470 A t s f x p')). Qed.
Lemma lem7025813 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (x : A) (p' : Prop) : term471 A t s f x p'.
Proof. exact (EQ_MP (@lem7025812 A t s f x p') (@lem7025811 A t s f x p')). Qed.
Lemma lem7025814 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (x : A) (p' : Prop) (q' : Prop) : term472 A t s f x p' q'.
Proof. exact (@lem7025813 A t s f x p' q'). Qed.
Lemma lem7025815 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (x : A) (p' : Prop) (q' : Prop) : (term472 A t s f x p' q') = (term473 A t s f x p' q').
Proof. exact (eq_refl (term472 A t s f x p' q')). Qed.
Lemma lem7025816 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (x : A) (p' : Prop) (q' : Prop) : term473 A t s f x p' q'.
Proof. exact (EQ_MP (@lem7025815 A t s f x p' q') (@lem7025814 A t s f x p' q')). Qed.
Lemma lem7025818 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term458 A x s t) = (term304 A s x t).
Proof. exact (EQ_MP (@lem7025555 A s x t) (@lem7025554 A s t x)). Qed.
Lemma lem7025819 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term458 A x s t) = (term304 A s x t).
Proof. exact (@lem7025818 A s x t). Qed.
Lemma lem7025820 {A : Type'} (t : A -> Prop) (x : A) (s : type686 A) : (term469 A x t s) = (term474 A t x s).
Proof. exact (@lem7025819 A t x (@UNIONS A s)). Qed.
Lemma lem7025824 {A : Type'} (s : type686 A) (x : A) : (term451 A x s) = (term452 A s x).
Proof. exact (EQ_MP (@lem7025546 A s x) (@lem7025545 A s x)). Qed.
Lemma lem7025825 {A : Type'} (s : type686 A) (x : A) : (term451 A x s) = (term452 A s x).
Proof. exact (@lem7025824 A s x). Qed.
Lemma lem7025844 {A : Type'} (x : A) (t : A -> Prop) : (term425 A x t) = (term425 A x t).
Proof. exact (eq_refl (term425 A x t)). Qed.
Lemma lem7025845 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) : (term474 A t x s) = (term475 A t s x).
Proof. exact (MK_COMB (@lem7025844 A x t) (@lem7025825 A s x)). Qed.
Lemma lem7025866 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) : (term469 A x t s) = (term475 A t s x).
Proof. exact (TRANS (@lem7025820 A t x s) (@lem7025845 A t s x)). Qed.
Lemma lem7025867 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (q' : Prop) : term476 A f t s x q'.
Proof. exact (@lem7025816 A t s f x (term475 A t s x) q'). Qed.
Lemma lem7025868 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (q' : Prop) : term477 A f t s x q'.
Proof. exact (@lem7025867 A f t s x q' (@lem7025866 A t s x)). Qed.
Lemma lem7025909 {A : Type'} (f : A -> nat) (x : A) : ((f x) = (NUMERAL 0)) = ((f x) = (NUMERAL 0)).
Proof. exact (eq_refl ((f x) = (NUMERAL 0))). Qed.
Lemma lem7025910 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (x : A) : term478 A t s f x.
Proof. exact (fun h0 : term475 A t s x => @lem7025909 A f x). Qed.
Lemma lem7025911 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (x : A) : term479 A t s f x.
Proof. exact (@lem7025868 A f t s x ((f x) = (NUMERAL 0))). Qed.
Lemma lem7025912 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (x : A) : (term480 A t s f x) = (term481 A t s f x).
Proof. exact (@lem7025911 A t s f x (@lem7025910 A t s f x)). Qed.
Lemma lem7026046 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term482 A t s f) = (term483 A t s f).
Proof. exact (fun_ext (fun x : A => @lem7025912 A t s f x)). Qed.
Lemma lem7026180 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7026181 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term484 A t s f) = (term485 A t s f).
Proof. exact (MK_COMB (@lem7026180 A) (@lem7026046 A t s f)). Qed.
Lemma lem7026319 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) (h2 : @FINITE (A -> Prop) s) : (term486 A t s f) = (term487 A t s f).
Proof. exact (MK_COMB (@lem7025799 A t s h1 h2) (@lem7026181 A t s f)). Qed.
Lemma lem7026321 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7026322 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term487 A t s f) = (term485 A t s f).
Proof. exact (@lem7026321 (term485 A t s f)). Qed.
Lemma lem7026460 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) (h2 : @FINITE (A -> Prop) s) : (term486 A t s f) = (term485 A t s f).
Proof. exact (TRANS (@lem7026319 A f t s h1 h2) (@lem7026322 A t s f)). Qed.
Lemma lem7026461 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) (h2 : @FINITE (A -> Prop) s) (h3 : term216 A t s) : (term488 A t s f) = (term487 A t s f).
Proof. exact (MK_COMB (@lem7025669 A t s h1 h3) (@lem7026460 A f t s h1 h2)). Qed.
Lemma lem7026463 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7026464 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term487 A t s f) = (term485 A t s f).
Proof. exact (@lem7026463 (term485 A t s f)). Qed.
Lemma lem7026602 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) (h2 : @FINITE (A -> Prop) s) (h3 : term216 A t s) : (term488 A t s f) = (term485 A t s f).
Proof. exact (TRANS (@lem7026461 A f t s h1 h2 h3) (@lem7026464 A t s f)). Qed.
Lemma lem7026603 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) (h2 : @FINITE (A -> Prop) s) (h3 : term216 A t s) : (term485 A t s f) = (term488 A t s f).
Proof. exact (SYM (@lem7026602 A f t s h1 h2 h3)). Qed.
Lemma lem7026605 (p : Prop) : p = (term260 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7026606 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term485 A t s f) = (term489 A t s f).
Proof. exact (@lem7026605 (term485 A t s f)). Qed.
Lemma lem7026607 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term489 A t s f) = (term485 A t s f).
Proof. exact (SYM (@lem7026606 A t s f)). Qed.
Lemma lem7026608 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term490 A t s f) : term490 A t s f.
Proof. exact (h1). Qed.
Lemma lem7026611 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term491 A t s f) : term491 A t s f.
Proof. exact (h1). Qed.
Lemma lem7026612 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : term492 A t s f.
Proof. exact (fun h0 : term491 A t s f => @lem7026611 A t s f h0). Qed.
Lemma lem7026613 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term492 A t s f) : term492 A t s f.
Proof. exact (h1). Qed.
Lemma lem7026614 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term491 A t s f) : term491 A t s f.
Proof. exact (h1). Qed.
Lemma lem7026615 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term491 A t s f) (h2 : term492 A t s f) : term491 A t s f.
Proof. exact (@lem7026613 A t s f h2 (@lem7026614 A t s f h1)). Qed.
Lemma lem7026616 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term491 A t s f) : term493 A t s f.
Proof. exact (fun h0 : term492 A t s f => @lem7026615 A t s f h1 h0). Qed.
Lemma lem7026617 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term492 A t s f) : term492 A t s f.
Proof. exact (h1). Qed.
Lemma lem7026618 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term491 A t s f) (h2 : term492 A t s f) : term491 A t s f.
Proof. exact (@lem7026616 A t s f h1 (@lem7026617 A t s f h2)). Qed.
Lemma lem7026619 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term492 A t s f) : term492 A t s f.
Proof. exact (fun h0 : term491 A t s f => @lem7026618 A t s f h0 h1). Qed.
Lemma lem7026620 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : term494 A t s f.
Proof. exact (fun h0 : term492 A t s f => @lem7026619 A t s f h0). Qed.
Lemma lem7026623 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : term492 A t s f.
Proof. exact (@lem7026620 A t s f (@lem7026612 A t s f)). Qed.
Lemma lem7026624 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : term492 A t s f.
Proof. exact (@lem7026623 A t s f). Qed.
Lemma lem7026680 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7026681 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term489 A t s f) = (term495 A t s f).
Proof. exact (@lem7026680 (term490 A t s f)). Qed.
Lemma lem7026683 (t : Prop) : (term268 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7026684 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term495 A t s f) = (term485 A t s f).
Proof. exact (@lem7026683 (term485 A t s f)). Qed.
Lemma lem7026689 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term489 A t s f) = (term485 A t s f).
Proof. exact (TRANS (@lem7026681 A t s f) (@lem7026684 A t s f)). Qed.
Lemma lem7026744 {A : Type'} (s : type686 A) : (term84 A s) = (term84 A s).
Proof. exact (eq_refl (term84 A s)). Qed.
Lemma lem7026745 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term496 A t s f) = (term497 A t s f).
Proof. exact (MK_COMB (@lem7026744 A s) (@lem7026689 A t s f)). Qed.
Lemma lem7026748 {A : Type'} (t : A -> Prop) (s : type686 A) : (term498 A t s) = (term498 A t s).
Proof. exact (eq_refl (term498 A t s)). Qed.
Lemma lem7026749 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term499 A t s f) = (term500 A t s f).
Proof. exact (MK_COMB (@lem7026748 A t s) (@lem7026745 A t s f)). Qed.
Lemma lem7026752 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term269 A t s f) = (term269 A t s f).
Proof. exact (eq_refl (term269 A t s f)). Qed.
Lemma lem7026753 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term501 A t s f) = (term502 A t s f).
Proof. exact (MK_COMB (@lem7026752 A t s f) (@lem7026749 A t s f)). Qed.
Lemma lem7026756 {A : Type'} (t : A -> Prop) (s : type686 A) : (term272 A t s) = (term272 A t s).
Proof. exact (eq_refl (term272 A t s)). Qed.
Lemma lem7026757 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term491 A t s f) = (term503 A t s f).
Proof. exact (MK_COMB (@lem7026756 A t s) (@lem7026753 A t s f)). Qed.
Lemma lem7026760 {A : Type'} (s : type686 A) (f : A -> nat) : (term504 A s f) = (term505 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7026757 A t s f)). Qed.
Lemma lem7026761 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7026762 {A : Type'} (s : type686 A) (f : A -> nat) : (term506 A s f) = (term507 A s f).
Proof. exact (MK_COMB (@lem7026761 A) (@lem7026760 A s f)). Qed.
Lemma lem7026767 {A : Type'} (f : A -> nat) : (term508 A f) = (term509 A f).
Proof. exact (fun_ext (fun s : type686 A => @lem7026762 A s f)). Qed.
Lemma lem7026768 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem7026769 {A : Type'} (f : A -> nat) : (term510 A f) = (term511 A f).
Proof. exact (MK_COMB (@lem7026768 A) (@lem7026767 A f)). Qed.
Lemma lem7026774 {A : Type'} : (term512 A) = (term513 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem7026769 A f)). Qed.
Lemma lem7026775 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7026784 {A : Type'} : (term514 A) = (term515 A).
Proof. exact (MK_COMB (@lem7026775 A) (@lem7026774 A)). Qed.
Lemma lem7026785 {A : Type'} (f : A -> nat) (x : A) : ((f x) = (NUMERAL 0)) = ((f x) = (NUMERAL 0)).
Proof. exact (eq_refl ((f x) = (NUMERAL 0))). Qed.
Lemma lem7026790 {A : Type'} (s : type686 A) (x : A) (t : A -> Prop) : (term516 A s x t) = (term516 A s x t).
Proof. exact (eq_refl (term516 A s x t)). Qed.
Lemma lem7026791 {A : Type'} (s : type686 A) (x : A) : (term517 A s x) = (term517 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7026790 A s x t)). Qed.
Lemma lem7026792 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem7026793 {A : Type'} (s : type686 A) (x : A) : (term452 A s x) = (term452 A s x).
Proof. exact (MK_COMB (@lem7026792 A) (@lem7026791 A s x)). Qed.
Lemma lem7026796 {A : Type'} (x : A) (t : A -> Prop) : (term425 A x t) = (term425 A x t).
Proof. exact (eq_refl (term425 A x t)). Qed.
Lemma lem7026797 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) : (term475 A t s x) = (term475 A t s x).
Proof. exact (MK_COMB (@lem7026796 A x t) (@lem7026793 A s x)). Qed.
Lemma lem7026798 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7026799 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) : (term518 A t s x) = (term518 A t s x).
Proof. exact (MK_COMB (@lem7026798) (@lem7026797 A t s x)). Qed.
Lemma lem7026800 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (x : A) : (term481 A t s f x) = (term481 A t s f x).
Proof. exact (MK_COMB (@lem7026799 A t s x) (@lem7026785 A f x)). Qed.
Lemma lem7026801 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term483 A t s f) = (term483 A t s f).
Proof. exact (fun_ext (fun x : A => @lem7026800 A t s f x)). Qed.
Lemma lem7026802 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7026803 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term485 A t s f) = (term485 A t s f).
Proof. exact (MK_COMB (@lem7026802 A) (@lem7026801 A t s f)). Qed.
Lemma lem7026806 {A : Type'} (s : type686 A) : (term84 A s) = (term84 A s).
Proof. exact (eq_refl (term84 A s)). Qed.
Lemma lem7026807 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term497 A t s f) = (term497 A t s f).
Proof. exact (MK_COMB (@lem7026806 A s) (@lem7026803 A t s f)). Qed.
Lemma lem7026812 {A : Type'} (t : A -> Prop) (s : type686 A) : (term498 A t s) = (term498 A t s).
Proof. exact (eq_refl (term498 A t s)). Qed.
Lemma lem7026813 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term500 A t s f) = (term500 A t s f).
Proof. exact (MK_COMB (@lem7026812 A t s) (@lem7026807 A t s f)). Qed.
Lemma lem7026844 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) (x : A) : (term120 A t s t1 t2 f x) = (term120 A t s t1 t2 f x).
Proof. exact (eq_refl (term120 A t s t1 t2 f x)). Qed.
Lemma lem7026845 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) : (term122 A t s t1 t2 f) = (term122 A t s t1 t2 f).
Proof. exact (fun_ext (fun x : A => @lem7026844 A t s t1 t2 f x)). Qed.
Lemma lem7026846 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7026847 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) : (term124 A t s t1 t2 f) = (term124 A t s t1 t2 f).
Proof. exact (MK_COMB (@lem7026846 A) (@lem7026845 A t s t1 t2 f)). Qed.
Lemma lem7026848 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> nat) : (term126 A t s t1 f) = (term126 A t s t1 f).
Proof. exact (fun_ext (fun t2 : A -> Prop => @lem7026847 A t s t1 t2 f)). Qed.
Lemma lem7026849 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7026850 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> nat) : (term128 A t s t1 f) = (term128 A t s t1 f).
Proof. exact (MK_COMB (@lem7026849 A) (@lem7026848 A t s t1 f)). Qed.
Lemma lem7026851 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term130 A t s f) = (term130 A t s f).
Proof. exact (fun_ext (fun t1 : A -> Prop => @lem7026850 A t s t1 f)). Qed.
Lemma lem7026852 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7026853 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term132 A t s f) = (term132 A t s f).
Proof. exact (MK_COMB (@lem7026852 A) (@lem7026851 A t s f)). Qed.
Lemma lem7026854 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7026855 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term269 A t s f) = (term269 A t s f).
Proof. exact (MK_COMB (@lem7026854) (@lem7026853 A t s f)). Qed.
Lemma lem7026856 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term502 A t s f) = (term502 A t s f).
Proof. exact (MK_COMB (@lem7026855 A t s f) (@lem7026813 A t s f)). Qed.
Lemma lem7026865 {A : Type'} (t : A -> Prop) (s : type686 A) (t' : A -> Prop) : (term103 A t s t') = (term103 A t s t').
Proof. exact (eq_refl (term103 A t s t')). Qed.
Lemma lem7026866 {A : Type'} (t : A -> Prop) (s : type686 A) : (term105 A t s) = (term105 A t s).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem7026865 A t s t')). Qed.
Lemma lem7026867 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7026868 {A : Type'} (t : A -> Prop) (s : type686 A) : (term107 A t s) = (term107 A t s).
Proof. exact (MK_COMB (@lem7026867 A) (@lem7026866 A t s)). Qed.
Lemma lem7026869 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7026870 {A : Type'} (t : A -> Prop) (s : type686 A) : (term272 A t s) = (term272 A t s).
Proof. exact (MK_COMB (@lem7026869) (@lem7026868 A t s)). Qed.
Lemma lem7026871 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term503 A t s f) = (term503 A t s f).
Proof. exact (MK_COMB (@lem7026870 A t s) (@lem7026856 A t s f)). Qed.
Lemma lem7026872 {A : Type'} (s : type686 A) (f : A -> nat) : (term505 A s f) = (term505 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7026871 A t s f)). Qed.
Lemma lem7026873 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7026874 {A : Type'} (s : type686 A) (f : A -> nat) : (term507 A s f) = (term507 A s f).
Proof. exact (MK_COMB (@lem7026873 A) (@lem7026872 A s f)). Qed.
Lemma lem7026875 {A : Type'} (f : A -> nat) : (term509 A f) = (term509 A f).
Proof. exact (fun_ext (fun s : type686 A => @lem7026874 A s f)). Qed.
Lemma lem7026876 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem7026877 {A : Type'} (f : A -> nat) : (term511 A f) = (term511 A f).
Proof. exact (MK_COMB (@lem7026876 A) (@lem7026875 A f)). Qed.
Lemma lem7026878 {A : Type'} : (term513 A) = (term513 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem7026877 A f)). Qed.
Lemma lem7026879 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7026880 {A : Type'} : (term515 A) = (term515 A).
Proof. exact (MK_COMB (@lem7026879 A) (@lem7026878 A)). Qed.
Lemma lem7026969 {A : Type'} : (term514 A) = (term515 A).
Proof. exact (TRANS (@lem7026784 A) (@lem7026880 A)). Qed.
Lemma lem7026970 {A : Type'} : (term515 A) = (term514 A).
Proof. exact (SYM (@lem7026969 A)). Qed.
Lemma lem7026972 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term132 A t s f.
Proof. exact (h1). Qed.
Lemma lem7026975 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (h1 : term475 A t s x) : term475 A t s x.
Proof. exact (h1). Qed.
Lemma lem7026977 (p : Prop) : p = (term260 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7026978 {A : Type'} (f : A -> nat) (x : A) : ((f x) = (NUMERAL 0)) = (term292 A f x).
Proof. exact (@lem7026977 ((f x) = (NUMERAL 0))). Qed.
Lemma lem7026979 {A : Type'} (f : A -> nat) (x : A) : (term292 A f x) = ((f x) = (NUMERAL 0)).
Proof. exact (SYM (@lem7026978 A f x)). Qed.
Lemma lem7026980 {A : Type'} (f : A -> nat) (x : A) (h1 : term293 A f x) : term293 A f x.
Proof. exact (h1). Qed.
Lemma lem7027040 {A : Type'} (t : A -> Prop) (t1 : A -> Prop) (s : type686 A) : (term294 A t t1 s) = (term295 A t t1 s).
Proof. exact (@lem17160 (t1 = t) (@IN (A -> Prop) t1 s)). Qed.
Lemma lem7027047 {A : Type'} (t : A -> Prop) (t2 : A -> Prop) (s : type686 A) : (term294 A t t2 s) = (term295 A t t2 s).
Proof. exact (@lem17160 (t2 = t) (@IN (A -> Prop) t2 s)). Qed.
Lemma lem7027050 {A : Type'} (t1 : A -> Prop) (t2 : A -> Prop) : (term296 A t1 t2) = (t1 = t2).
Proof. exact (@lem16933 (t1 = t2)). Qed.
Lemma lem7027057 {A : Type'} (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term297 A t1 x t2) = (term298 A t1 x t2).
Proof. exact (@lem17045 (@IN A x t1) (@IN A x t2)). Qed.
Lemma lem7027058 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7027059 {A : Type'} (t1 : A -> Prop) (t2 : A -> Prop) : (term299 A t1 t2) = (term187 A t1 t2).
Proof. exact (MK_COMB (@lem7027058) (@lem7027050 A t1 t2)). Qed.
Lemma lem7027060 {A : Type'} (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term300 A t1 x t2) = (term301 A t1 x t2).
Proof. exact (MK_COMB (@lem7027059 A t1 t2) (@lem7027057 A t1 x t2)). Qed.
Lemma lem7027061 {A : Type'} (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term302 A t1 x t2) = (term300 A t1 x t2).
Proof. exact (@lem17045 (term303 A t1 t2) (term304 A t1 x t2)). Qed.
Lemma lem7027062 {A : Type'} (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term302 A t1 x t2) = (term301 A t1 x t2).
Proof. exact (TRANS (@lem7027061 A t1 x t2) (@lem7027060 A t1 x t2)). Qed.
Lemma lem7027063 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7027064 {A : Type'} (t : A -> Prop) (t2 : A -> Prop) (s : type686 A) : (term305 A t t2 s) = (term306 A t t2 s).
Proof. exact (MK_COMB (@lem7027063) (@lem7027047 A t t2 s)). Qed.
Lemma lem7027065 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term307 A t s t1 x t2) = (term308 A t s t1 x t2).
Proof. exact (MK_COMB (@lem7027064 A t t2 s) (@lem7027062 A t1 x t2)). Qed.
Lemma lem7027066 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term309 A t s t1 x t2) = (term307 A t s t1 x t2).
Proof. exact (@lem17045 (term99 A t t2 s) (term112 A t1 x t2)). Qed.
Lemma lem7027067 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term309 A t s t1 x t2) = (term308 A t s t1 x t2).
Proof. exact (TRANS (@lem7027066 A t s t1 x t2) (@lem7027065 A t s t1 x t2)). Qed.
Lemma lem7027068 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7027069 {A : Type'} (t : A -> Prop) (t1 : A -> Prop) (s : type686 A) : (term305 A t t1 s) = (term306 A t t1 s).
Proof. exact (MK_COMB (@lem7027068) (@lem7027040 A t t1 s)). Qed.
Lemma lem7027070 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term310 A t s t1 x t2) = (term311 A t s t1 x t2).
Proof. exact (MK_COMB (@lem7027069 A t t1 s) (@lem7027067 A t s t1 x t2)). Qed.
Lemma lem7027071 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term312 A t s t1 x t2) = (term310 A t s t1 x t2).
Proof. exact (@lem17045 (term99 A t t1 s) (term114 A t s t1 x t2)). Qed.
Lemma lem7027072 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term312 A t s t1 x t2) = (term311 A t s t1 x t2).
Proof. exact (TRANS (@lem7027071 A t s t1 x t2) (@lem7027070 A t s t1 x t2)). Qed.
Lemma lem7027073 {A : Type'} (f : A -> nat) (x : A) : ((f x) = (NUMERAL 0)) = ((f x) = (NUMERAL 0)).
Proof. exact (eq_refl ((f x) = (NUMERAL 0))). Qed.
Lemma lem7027074 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7027075 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term313 A t s t1 x t2) = (term314 A t s t1 x t2).
Proof. exact (MK_COMB (@lem7027074) (@lem7027072 A t s t1 x t2)). Qed.
Lemma lem7027076 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) (x : A) : (term315 A t s t1 t2 f x) = (term316 A t s t1 t2 f x).
Proof. exact (MK_COMB (@lem7027075 A t s t1 x t2) (@lem7027073 A f x)). Qed.
Lemma lem7027077 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) (x : A) : (term120 A t s t1 t2 f x) = (term315 A t s t1 t2 f x).
Proof. exact (@lem17265 (term116 A t s t1 x t2) ((f x) = (NUMERAL 0))). Qed.
Lemma lem7027078 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) (x : A) : (term120 A t s t1 t2 f x) = (term316 A t s t1 t2 f x).
Proof. exact (TRANS (@lem7027077 A t s t1 t2 f x) (@lem7027076 A t s t1 t2 f x)). Qed.
Lemma lem7027079 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) : (term122 A t s t1 t2 f) = (term317 A t s t1 t2 f).
Proof. exact (fun_ext (fun x : A => @lem7027078 A t s t1 t2 f x)). Qed.
Lemma lem7027080 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7027081 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) : (term124 A t s t1 t2 f) = (term318 A t s t1 t2 f).
Proof. exact (MK_COMB (@lem7027080 A) (@lem7027079 A t s t1 t2 f)). Qed.
Lemma lem7027082 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> nat) : (term126 A t s t1 f) = (term319 A t s t1 f).
Proof. exact (fun_ext (fun t2 : A -> Prop => @lem7027081 A t s t1 t2 f)). Qed.
Lemma lem7027083 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7027084 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> nat) : (term128 A t s t1 f) = (term320 A t s t1 f).
Proof. exact (MK_COMB (@lem7027083 A) (@lem7027082 A t s t1 f)). Qed.
Lemma lem7027085 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term130 A t s f) = (term321 A t s f).
Proof. exact (fun_ext (fun t1 : A -> Prop => @lem7027084 A t s t1 f)). Qed.
Lemma lem7027086 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7027147 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term132 A t s f) = (term322 A t s f).
Proof. exact (MK_COMB (@lem7027086 A) (@lem7027085 A t s f)). Qed.
Lemma lem7027148 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term322 A t s f.
Proof. exact (EQ_MP (@lem7027147 A t s f) (@lem7026972 A t s f h1)). Qed.
Lemma lem7027154 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term216 A t s) : term216 A t s.
Proof. exact (h1). Qed.
Lemma lem7027166 {A : Type'} (s : type686 A) (x : A) (t : A -> Prop) : (term516 A s x t) = (term516 A s x t).
Proof. exact (eq_refl (term516 A s x t)). Qed.
Lemma lem7027167 {A : Type'} (s : type686 A) (x : A) : (term517 A s x) = (term517 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7027166 A s x t)). Qed.
Lemma lem7027168 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem7027169 {A : Type'} (s : type686 A) (x : A) : (term452 A s x) = (term452 A s x).
Proof. exact (MK_COMB (@lem7027168 A) (@lem7027167 A s x)). Qed.
Lemma lem7027171 {A : Type'} (x : A) (t : A -> Prop) : (term425 A x t) = (term425 A x t).
Proof. exact (eq_refl (term425 A x t)). Qed.
Lemma lem7027172 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) : (term475 A t s x) = (term475 A t s x).
Proof. exact (MK_COMB (@lem7027171 A x t) (@lem7027169 A s x)). Qed.
Lemma lem7027223 {A : Type'} (P : Prop) (Q : A -> Prop) : (term519 A P Q) = (term520 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7027224 {A : Type'} (P : Prop) (Q : type686 A) : (term521 A P Q) = (term522 A P Q).
Proof. exact (@lem7027223 (A -> Prop) P Q). Qed.
Lemma lem7027225 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) : (term523 A t s x) = (term524 A t s x).
Proof. exact (@lem7027224 A (@IN A x t) (term517 A s x)). Qed.
Lemma lem7027226 {A : Type'} (s : type686 A) (x : A) (t : A -> Prop) : (term525 A s x t) = (term516 A s x t).
Proof. exact (eq_refl (term525 A s x t)). Qed.
Lemma lem7027227 {A : Type'} (s : type686 A) (x : A) : (term526 A s x) = (term517 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7027226 A s x t)). Qed.
Lemma lem7027228 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem7027229 {A : Type'} (s : type686 A) (x : A) : (term527 A s x) = (term452 A s x).
Proof. exact (MK_COMB (@lem7027228 A) (@lem7027227 A s x)). Qed.
Lemma lem7027230 {A : Type'} (x : A) (t : A -> Prop) : (term425 A x t) = (term425 A x t).
Proof. exact (eq_refl (term425 A x t)). Qed.
Lemma lem7027231 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) : (term523 A t s x) = (term475 A t s x).
Proof. exact (MK_COMB (@lem7027230 A x t) (@lem7027229 A s x)). Qed.
Lemma lem7027232 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7027233 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) : (term528 A t s x) = (term529 A t s x).
Proof. exact (MK_COMB (@lem7027232) (@lem7027231 A t s x)). Qed.
Lemma lem7027234 {A : Type'} (s : type686 A) (x : A) (t' : A -> Prop) : (term525 A s x t') = (term516 A s x t').
Proof. exact (eq_refl (term525 A s x t')). Qed.
Lemma lem7027235 {A : Type'} (x : A) (t : A -> Prop) : (term425 A x t) = (term425 A x t).
Proof. exact (eq_refl (term425 A x t)). Qed.
Lemma lem7027236 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) : (term530 A t s x t') = (term531 A t s x t').
Proof. exact (MK_COMB (@lem7027235 A x t) (@lem7027234 A s x t')). Qed.
Lemma lem7027237 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) : (term532 A t s x) = (term533 A t s x).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem7027236 A t s x t')). Qed.
Lemma lem7027238 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem7027239 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) : (term524 A t s x) = (term534 A t s x).
Proof. exact (MK_COMB (@lem7027238 A) (@lem7027237 A t s x)). Qed.
Lemma lem7027240 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) : ((term523 A t s x) = (term524 A t s x)) = ((term475 A t s x) = (term534 A t s x)).
Proof. exact (MK_COMB (@lem7027233 A t s x) (@lem7027239 A t s x)). Qed.
Lemma lem7027242 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) : (term475 A t s x) = (term534 A t s x).
Proof. exact (EQ_MP (@lem7027240 A t s x) (@lem7027225 A t s x)). Qed.
Lemma lem7027243 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) : (term475 A t s x) = (term534 A t s x).
Proof. exact (TRANS (@lem7027172 A t s x) (@lem7027242 A t s x)). Qed.
Lemma lem7027244 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (h1 : term475 A t s x) : term534 A t s x.
Proof. exact (EQ_MP (@lem7027243 A t s x) (@lem7026975 A t s x h1)). Qed.
Lemma lem7027250 {A : Type'} (f : A -> nat) (x : A) (h1 : term293 A f x) : term293 A f x.
Proof. exact (h1). Qed.
Lemma lem7027355 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) (x : A) : (term316 A t s t1 t2 f x) = (term316 A t s t1 t2 f x).
Proof. exact (eq_refl (term316 A t s t1 t2 f x)). Qed.
Lemma lem7027356 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) : (term317 A t s t1 t2 f) = (term317 A t s t1 t2 f).
Proof. exact (fun_ext (fun x : A => @lem7027355 A t s t1 t2 f x)). Qed.
Lemma lem7027357 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7027358 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) : (term318 A t s t1 t2 f) = (term318 A t s t1 t2 f).
Proof. exact (MK_COMB (@lem7027357 A) (@lem7027356 A t s t1 t2 f)). Qed.
Lemma lem7027359 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> nat) : (term319 A t s t1 f) = (term319 A t s t1 f).
Proof. exact (fun_ext (fun t2 : A -> Prop => @lem7027358 A t s t1 t2 f)). Qed.
Lemma lem7027360 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7027361 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> nat) : (term320 A t s t1 f) = (term320 A t s t1 f).
Proof. exact (MK_COMB (@lem7027360 A) (@lem7027359 A t s t1 f)). Qed.
Lemma lem7027362 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term321 A t s f) = (term321 A t s f).
Proof. exact (fun_ext (fun t1 : A -> Prop => @lem7027361 A t s t1 f)). Qed.
Lemma lem7027363 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7027364 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term322 A t s f) = (term322 A t s f).
Proof. exact (MK_COMB (@lem7027363 A) (@lem7027362 A t s f)). Qed.
Lemma lem7027365 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term322 A t s f.
Proof. exact (EQ_MP (@lem7027364 A t s f) (@lem7027148 A t s f h1)). Qed.
Lemma lem7027373 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term216 A t s) : term216 A t s.
Proof. exact (h1). Qed.
Lemma lem7027389 {A : Type'} (f : A -> nat) (x : A) (h1 : term293 A f x) : term293 A f x.
Proof. exact (h1). Qed.
Lemma lem7027411 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term531 A t s x t') : term531 A t s x t'.
Proof. exact (h1). Qed.
Lemma lem7027412 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term531 A t s x t') : term516 A s x t'.
Proof. exact (proj2 (@lem7027411 A t s x t' h1)). Qed.
Lemma lem7027440 {A : Type'} (f : A -> nat) (x : A) : ((f x) = (NUMERAL 0)) = ((f x) = (NUMERAL 0)).
Proof. exact (eq_refl ((f x) = (NUMERAL 0))). Qed.
Lemma lem7027469 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term308 A t s t1 x t2) = (term325 A t s t1 x t2).
Proof. exact (@lem19699 (term303 A t2 t) (term216 A t2 s) (term301 A t1 x t2)). Qed.
Lemma lem7027476 {A : Type'} (t : A -> Prop) (t1 : A -> Prop) (s : type686 A) : (term306 A t t1 s) = (term306 A t t1 s).
Proof. exact (eq_refl (term306 A t t1 s)). Qed.
Lemma lem7027477 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term311 A t s t1 x t2) = (term326 A t s t1 x t2).
Proof. exact (MK_COMB (@lem7027476 A t t1 s) (@lem7027469 A t s t1 x t2)). Qed.
Lemma lem7027478 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term326 A t s t1 x t2) = (term327 A t s t1 x t2).
Proof. exact (@lem19490 (term328 A t t1 x t2) (term295 A t t1 s) (term329 A s t1 x t2)). Qed.
Lemma lem7027485 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term330 A t s t1 x t2) = (term331 A t s t1 x t2).
Proof. exact (@lem19699 (term303 A t1 t) (term216 A t1 s) (term329 A s t1 x t2)). Qed.
Lemma lem7027492 {A : Type'} (s : type686 A) (t : A -> Prop) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term332 A s t t1 x t2) = (term333 A s t t1 x t2).
Proof. exact (@lem19699 (term303 A t1 t) (term216 A t1 s) (term328 A t t1 x t2)). Qed.
Lemma lem7027493 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7027494 {A : Type'} (s : type686 A) (t : A -> Prop) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term334 A s t t1 x t2) = (term335 A s t t1 x t2).
Proof. exact (MK_COMB (@lem7027493) (@lem7027492 A s t t1 x t2)). Qed.
Lemma lem7027495 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term327 A t s t1 x t2) = (term336 A t s t1 x t2).
Proof. exact (MK_COMB (@lem7027494 A s t t1 x t2) (@lem7027485 A t s t1 x t2)). Qed.
Lemma lem7027496 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term326 A t s t1 x t2) = (term336 A t s t1 x t2).
Proof. exact (TRANS (@lem7027478 A t s t1 x t2) (@lem7027495 A t s t1 x t2)). Qed.
Lemma lem7027497 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term311 A t s t1 x t2) = (term336 A t s t1 x t2).
Proof. exact (TRANS (@lem7027477 A t s t1 x t2) (@lem7027496 A t s t1 x t2)). Qed.
Lemma lem7027498 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7027499 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term314 A t s t1 x t2) = (term337 A t s t1 x t2).
Proof. exact (MK_COMB (@lem7027498) (@lem7027497 A t s t1 x t2)). Qed.
Lemma lem7027500 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) (x : A) : (term316 A t s t1 t2 f x) = (term338 A t s t1 t2 f x).
Proof. exact (MK_COMB (@lem7027499 A t s t1 x t2) (@lem7027440 A f x)). Qed.
Lemma lem7027501 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) (x : A) : (term338 A t s t1 t2 f x) = (term339 A t s t1 t2 f x).
Proof. exact (@lem19699 (term333 A s t t1 x t2) (term331 A t s t1 x t2) ((f x) = (NUMERAL 0))). Qed.
Lemma lem7027508 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) (x : A) : (term340 A t s t1 t2 f x) = (term341 A t s t1 t2 f x).
Proof. exact (@lem19699 (term342 A t s t1 x t2) (term343 A s t1 x t2) ((f x) = (NUMERAL 0))). Qed.
Lemma lem7027515 {A : Type'} (s : type686 A) (t : A -> Prop) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) (x : A) : (term344 A s t t1 t2 f x) = (term345 A s t t1 t2 f x).
Proof. exact (@lem19699 (term346 A t t1 x t2) (term347 A s t t1 x t2) ((f x) = (NUMERAL 0))). Qed.
Lemma lem7027516 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7027517 {A : Type'} (s : type686 A) (t : A -> Prop) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) (x : A) : (term348 A s t t1 t2 f x) = (term349 A s t t1 t2 f x).
Proof. exact (MK_COMB (@lem7027516) (@lem7027515 A s t t1 t2 f x)). Qed.
Lemma lem7027518 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) (x : A) : (term339 A t s t1 t2 f x) = (term350 A t s t1 t2 f x).
Proof. exact (MK_COMB (@lem7027517 A s t t1 t2 f x) (@lem7027508 A t s t1 t2 f x)). Qed.
Lemma lem7027519 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) (x : A) : (term338 A t s t1 t2 f x) = (term350 A t s t1 t2 f x).
Proof. exact (TRANS (@lem7027501 A t s t1 t2 f x) (@lem7027518 A t s t1 t2 f x)). Qed.
Lemma lem7027520 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) (x : A) : (term316 A t s t1 t2 f x) = (term350 A t s t1 t2 f x).
Proof. exact (TRANS (@lem7027500 A t s t1 t2 f x) (@lem7027519 A t s t1 t2 f x)). Qed.
Lemma lem7027521 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) : (term317 A t s t1 t2 f) = (term351 A t s t1 t2 f).
Proof. exact (fun_ext (fun x : A => @lem7027520 A t s t1 t2 f x)). Qed.
Lemma lem7027522 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7027523 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> nat) : (term318 A t s t1 t2 f) = (term352 A t s t1 t2 f).
Proof. exact (MK_COMB (@lem7027522 A) (@lem7027521 A t s t1 t2 f)). Qed.
Lemma lem7027524 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> nat) : (term319 A t s t1 f) = (term353 A t s t1 f).
Proof. exact (fun_ext (fun t2 : A -> Prop => @lem7027523 A t s t1 t2 f)). Qed.
Lemma lem7027525 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7027526 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> nat) : (term320 A t s t1 f) = (term354 A t s t1 f).
Proof. exact (MK_COMB (@lem7027525 A) (@lem7027524 A t s t1 f)). Qed.
Lemma lem7027527 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term321 A t s f) = (term355 A t s f).
Proof. exact (fun_ext (fun t1 : A -> Prop => @lem7027526 A t s t1 f)). Qed.
Lemma lem7027528 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7027530 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term322 A t s f) = (term356 A t s f).
Proof. exact (MK_COMB (@lem7027528 A) (@lem7027527 A t s f)). Qed.
Lemma lem7027531 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term356 A t s f.
Proof. exact (EQ_MP (@lem7027530 A t s f) (@lem7027365 A t s f h1)). Qed.
Lemma lem7027535 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term216 A t s) : term216 A t s.
Proof. exact (h1). Qed.
Lemma lem7027543 {A : Type'} (f : A -> nat) (x : A) (h1 : term293 A f x) : term293 A f x.
Proof. exact (h1). Qed.
Lemma lem7027559 {A : Type'} (_93864 : A -> Prop) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term357 A t s f _93864.
Proof. exact (@lem7027531 A t s f h1 _93864). Qed.
Lemma lem7027560 {A : Type'} (t : A -> Prop) (s : type686 A) (_93864 : A -> Prop) (f : A -> nat) : (term357 A t s f _93864) = (term354 A t s _93864 f).
Proof. exact (eq_refl (term357 A t s f _93864)). Qed.
Lemma lem7027561 {A : Type'} (_93864 : A -> Prop) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term354 A t s _93864 f.
Proof. exact (EQ_MP (@lem7027560 A t s _93864 f) (@lem7027559 A _93864 t s f h1)). Qed.
Lemma lem7027562 {A : Type'} (_93864 : A -> Prop) (_93865 : A -> Prop) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term358 A t s _93864 f _93865.
Proof. exact (@lem7027561 A _93864 t s f h1 _93865). Qed.
Lemma lem7027563 {A : Type'} (t : A -> Prop) (s : type686 A) (_93864 : A -> Prop) (_93865 : A -> Prop) (f : A -> nat) : (term358 A t s _93864 f _93865) = (term352 A t s _93864 _93865 f).
Proof. exact (eq_refl (term358 A t s _93864 f _93865)). Qed.
Lemma lem7027564 {A : Type'} (_93864 : A -> Prop) (_93865 : A -> Prop) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term352 A t s _93864 _93865 f.
Proof. exact (EQ_MP (@lem7027563 A t s _93864 _93865 f) (@lem7027562 A _93864 _93865 t s f h1)). Qed.
Lemma lem7027565 {A : Type'} (_93864 : A -> Prop) (_93865 : A -> Prop) (_93866 : A) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term359 A t s _93864 _93865 f _93866.
Proof. exact (@lem7027564 A _93864 _93865 t s f h1 _93866). Qed.
Lemma lem7027566 {A : Type'} (t : A -> Prop) (s : type686 A) (_93864 : A -> Prop) (_93865 : A -> Prop) (f : A -> nat) (_93866 : A) : (term359 A t s _93864 _93865 f _93866) = (term350 A t s _93864 _93865 f _93866).
Proof. exact (eq_refl (term359 A t s _93864 _93865 f _93866)). Qed.
Lemma lem7027567 {A : Type'} (_93864 : A -> Prop) (_93865 : A -> Prop) (_93866 : A) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term350 A t s _93864 _93865 f _93866.
Proof. exact (EQ_MP (@lem7027566 A t s _93864 _93865 f _93866) (@lem7027565 A _93864 _93865 _93866 t s f h1)). Qed.
Lemma lem7027569 {A : Type'} (_93864 : A -> Prop) (_93865 : A -> Prop) (_93866 : A) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term345 A s t _93864 _93865 f _93866.
Proof. exact (proj1 (@lem7027567 A _93864 _93865 _93866 t s f h1)). Qed.
Lemma lem7027572 {A : Type'} (_93864 : A -> Prop) (_93865 : A -> Prop) (_93866 : A) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term535 A s t _93864 _93865 f _93866.
Proof. exact (proj2 (@lem7027569 A _93864 _93865 _93866 t s f h1)). Qed.
Lemma lem7027577 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term216 A t s) : term216 A t s.
Proof. exact (h1). Qed.
Lemma lem7027581 {A : Type'} (f : A -> nat) (x : A) (h1 : term293 A f x) : term293 A f x.
Proof. exact (h1). Qed.
Lemma lem7027681 {A : Type'} (s : type686 A) (t : A -> Prop) (_93864 : A -> Prop) (_93865 : A -> Prop) (f : A -> nat) (_93866 : A) : (term535 A s t _93864 _93865 f _93866) = (term536 A s t _93864 _93865 f _93866).
Proof. exact (@lem7018623 (term216 A _93864 s) (term328 A t _93864 _93866 _93865) ((f _93866) = (NUMERAL 0))). Qed.
Lemma lem7027682 {A : Type'} (t : A -> Prop) (_93864 : A -> Prop) (_93865 : A -> Prop) (f : A -> nat) (_93866 : A) : (term537 A t _93864 _93865 f _93866) = (term538 A t _93864 _93865 f _93866).
Proof. exact (@lem7018623 (term303 A _93865 t) (term301 A _93864 _93866 _93865) ((f _93866) = (NUMERAL 0))). Qed.
Lemma lem7027683 {A : Type'} (_93864 : A -> Prop) (_93865 : A -> Prop) (f : A -> nat) (_93866 : A) : (term364 A _93864 _93865 f _93866) = (term365 A _93864 _93865 f _93866).
Proof. exact (@lem7018623 (_93864 = _93865) (term298 A _93864 _93866 _93865) ((f _93866) = (NUMERAL 0))). Qed.
Lemma lem7027690 {A : Type'} (_93864 : A -> Prop) (_93865 : A -> Prop) (f : A -> nat) (_93866 : A) : (term366 A _93864 _93865 f _93866) = (term367 A _93864 _93865 f _93866).
Proof. exact (@lem7018623 (term368 A _93866 _93864) (term368 A _93866 _93865) ((f _93866) = (NUMERAL 0))). Qed.
Lemma lem7027691 {A : Type'} (_93864 : A -> Prop) (_93865 : A -> Prop) : (term187 A _93864 _93865) = (term187 A _93864 _93865).
Proof. exact (eq_refl (term187 A _93864 _93865)). Qed.
Lemma lem7027694 {A : Type'} (_93864 : A -> Prop) (_93865 : A -> Prop) (f : A -> nat) (_93866 : A) : (term365 A _93864 _93865 f _93866) = (term369 A _93864 _93865 f _93866).
Proof. exact (MK_COMB (@lem7027691 A _93864 _93865) (@lem7027690 A _93864 _93865 f _93866)). Qed.
Lemma lem7027695 {A : Type'} (_93864 : A -> Prop) (_93865 : A -> Prop) (f : A -> nat) (_93866 : A) : (term364 A _93864 _93865 f _93866) = (term369 A _93864 _93865 f _93866).
Proof. exact (TRANS (@lem7027683 A _93864 _93865 f _93866) (@lem7027694 A _93864 _93865 f _93866)). Qed.
Lemma lem7027696 {A : Type'} (_93865 : A -> Prop) (t : A -> Prop) : (term539 A _93865 t) = (term539 A _93865 t).
Proof. exact (eq_refl (term539 A _93865 t)). Qed.
Lemma lem7027699 {A : Type'} (t : A -> Prop) (_93864 : A -> Prop) (_93865 : A -> Prop) (f : A -> nat) (_93866 : A) : (term538 A t _93864 _93865 f _93866) = (term540 A t _93864 _93865 f _93866).
Proof. exact (MK_COMB (@lem7027696 A _93865 t) (@lem7027695 A _93864 _93865 f _93866)). Qed.
Lemma lem7027700 {A : Type'} (t : A -> Prop) (_93864 : A -> Prop) (_93865 : A -> Prop) (f : A -> nat) (_93866 : A) : (term537 A t _93864 _93865 f _93866) = (term540 A t _93864 _93865 f _93866).
Proof. exact (TRANS (@lem7027682 A t _93864 _93865 f _93866) (@lem7027699 A t _93864 _93865 f _93866)). Qed.
Lemma lem7027701 {A : Type'} (_93864 : A -> Prop) (s : type686 A) : (term370 A _93864 s) = (term370 A _93864 s).
Proof. exact (eq_refl (term370 A _93864 s)). Qed.
Lemma lem7027704 {A : Type'} (s : type686 A) (t : A -> Prop) (_93864 : A -> Prop) (_93865 : A -> Prop) (f : A -> nat) (_93866 : A) : (term536 A s t _93864 _93865 f _93866) = (term541 A s t _93864 _93865 f _93866).
Proof. exact (MK_COMB (@lem7027701 A _93864 s) (@lem7027700 A t _93864 _93865 f _93866)). Qed.
Lemma lem7027706 {A : Type'} (s : type686 A) (t : A -> Prop) (_93864 : A -> Prop) (_93865 : A -> Prop) (f : A -> nat) (_93866 : A) : (term535 A s t _93864 _93865 f _93866) = (term541 A s t _93864 _93865 f _93866).
Proof. exact (TRANS (@lem7027681 A s t _93864 _93865 f _93866) (@lem7027704 A s t _93864 _93865 f _93866)). Qed.
Lemma lem7027707 {A : Type'} (_93864 : A -> Prop) (_93865 : A -> Prop) (_93866 : A) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term541 A s t _93864 _93865 f _93866.
Proof. exact (EQ_MP (@lem7027706 A s t _93864 _93865 f _93866) (@lem7027572 A _93864 _93865 _93866 t s f h1)). Qed.
Lemma lem7027763 {A : Type'} : (@IN (A -> Prop)) = (@IN (A -> Prop)).
Proof. exact (eq_refl (@IN (A -> Prop))). Qed.
Lemma lem7027764 {A : Type'} (_93875 : A -> Prop) (_93877 : A -> Prop) (h1 : _93875 = _93877) : _93875 = _93877.
Proof. exact (h1). Qed.
Lemma lem7027765 {A : Type'} (_93876 : type686 A) (_93878 : type686 A) (h1 : _93876 = _93878) : _93876 = _93878.
Proof. exact (h1). Qed.
Lemma lem7027766 {A : Type'} (_93875 : A -> Prop) (_93877 : A -> Prop) (h1 : _93875 = _93877) : (@IN (A -> Prop) _93875) = (@IN (A -> Prop) _93877).
Proof. exact (MK_COMB (@lem7027763 A) (@lem7027764 A _93875 _93877 h1)). Qed.
Lemma lem7027767 {A : Type'} (_93875 : A -> Prop) (_93877 : A -> Prop) (_93876 : type686 A) (_93878 : type686 A) (h1 : _93875 = _93877) (h2 : _93876 = _93878) : (@IN (A -> Prop) _93875 _93876) = (@IN (A -> Prop) _93877 _93878).
Proof. exact (MK_COMB (@lem7027766 A _93875 _93877 h1) (@lem7027765 A _93876 _93878 h2)). Qed.
Lemma lem7027769 (b : Prop) (a : Prop) : term542 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem7027770 {A : Type'} (_93877 : A -> Prop) (_93878 : type686 A) (_93875 : A -> Prop) (_93876 : type686 A) : term543 A _93877 _93878 _93875 _93876.
Proof. exact (@lem7027769 (@IN (A -> Prop) _93877 _93878) (@IN (A -> Prop) _93875 _93876)). Qed.
Lemma lem7027771 {A : Type'} (_93875 : A -> Prop) (_93877 : A -> Prop) (_93876 : type686 A) (_93878 : type686 A) (h1 : _93875 = _93877) (h2 : _93876 = _93878) : term544 A _93877 _93878 _93875 _93876.
Proof. exact (@lem7027770 A _93877 _93878 _93875 _93876 (@lem7027767 A _93875 _93877 _93876 _93878 h1 h2)). Qed.
Lemma lem7027772 {A : Type'} (_93878 : type686 A) (_93876 : type686 A) (_93875 : A -> Prop) (_93877 : A -> Prop) (h1 : _93875 = _93877) : term545 A _93877 _93878 _93875 _93876.
Proof. exact (fun h0 : _93876 = _93878 => @lem7027771 A _93875 _93877 _93876 _93878 h1 h0). Qed.
Lemma lem7027774 (a : Prop) (b : Prop) : (a -> b) = (term546 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7027775 {A : Type'} (_93877 : A -> Prop) (_93878 : type686 A) (_93875 : A -> Prop) (_93876 : type686 A) : (term545 A _93877 _93878 _93875 _93876) = (term547 A _93877 _93878 _93875 _93876).
Proof. exact (@lem7027774 (_93876 = _93878) (term544 A _93877 _93878 _93875 _93876)). Qed.
Lemma lem7027776 {A : Type'} (_93878 : type686 A) (_93876 : type686 A) (_93875 : A -> Prop) (_93877 : A -> Prop) (h1 : _93875 = _93877) : term547 A _93877 _93878 _93875 _93876.
Proof. exact (EQ_MP (@lem7027775 A _93877 _93878 _93875 _93876) (@lem7027772 A _93878 _93876 _93875 _93877 h1)). Qed.
Lemma lem7027777 {A : Type'} (_93877 : A -> Prop) (_93878 : type686 A) (_93875 : A -> Prop) (_93876 : type686 A) : term548 A _93877 _93878 _93875 _93876.
Proof. exact (fun h0 : _93875 = _93877 => @lem7027776 A _93878 _93876 _93875 _93877 h0). Qed.
Lemma lem7027779 (a : Prop) (b : Prop) : (a -> b) = (term546 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7027780 {A : Type'} (_93877 : A -> Prop) (_93878 : type686 A) (_93875 : A -> Prop) (_93876 : type686 A) : (term548 A _93877 _93878 _93875 _93876) = (term549 A _93877 _93878 _93875 _93876).
Proof. exact (@lem7027779 (_93875 = _93877) (term547 A _93877 _93878 _93875 _93876)). Qed.
Lemma lem7027781 {A : Type'} (_93877 : A -> Prop) (_93878 : type686 A) (_93875 : A -> Prop) (_93876 : type686 A) : term549 A _93877 _93878 _93875 _93876.
Proof. exact (EQ_MP (@lem7027780 A _93877 _93878 _93875 _93876) (@lem7027777 A _93877 _93878 _93875 _93876)). Qed.
Lemma lem7027807 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term531 A t s x t') : @IN (A -> Prop) t' s.
Proof. exact (proj1 (@lem7027412 A t s x t' h1)). Qed.
Lemma lem7027808 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term531 A t s x t') : term373 A t' s.
Proof. exact (fun h0 : term216 A t' s => @lem7027807 A t s x t' h1). Qed.
Lemma lem7027810 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7027811 {A : Type'} (t' : A -> Prop) (s : type686 A) : (term373 A t' s) = (@IN (A -> Prop) t' s).
Proof. exact (@lem7027810 (@IN (A -> Prop) t' s)). Qed.
Lemma lem7027812 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term531 A t s x t') : @IN (A -> Prop) t' s.
Proof. exact (EQ_MP (@lem7027811 A t' s) (@lem7027808 A t s x t' h1)). Qed.
Lemma lem7027814 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem21386 (A -> Prop) x). Qed.
Lemma lem7027815 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem7027814 A x). Qed.
Lemma lem7027816 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (@lem7027815 A t). Qed.
Lemma lem7027817 {A : Type'} (t : A -> Prop) : term550 A t.
Proof. exact (fun h0 : term551 A t => @lem7027816 A t). Qed.
Lemma lem7027819 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7027820 {A : Type'} (t : A -> Prop) : (term550 A t) = (t = t).
Proof. exact (@lem7027819 (t = t)). Qed.
Lemma lem7027821 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (EQ_MP (@lem7027820 A t) (@lem7027817 A t)). Qed.
Lemma lem7027823 {A : Type'} (x : type686 A) : x = x.
Proof. exact (@lem21386 (type686 A) x). Qed.
Lemma lem7027824 {A : Type'} (x : type686 A) : x = x.
Proof. exact (@lem7027823 A x). Qed.
Lemma lem7027825 {A : Type'} (s : type686 A) : s = s.
Proof. exact (@lem7027824 A s). Qed.
Lemma lem7027826 {A : Type'} (s : type686 A) : term552 A s.
Proof. exact (fun h0 : term553 A s => @lem7027825 A s). Qed.
Lemma lem7027828 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7027829 {A : Type'} (s : type686 A) : (term552 A s) = (s = s).
Proof. exact (@lem7027828 (s = s)). Qed.
Lemma lem7027830 {A : Type'} (s : type686 A) : s = s.
Proof. exact (EQ_MP (@lem7027829 A s) (@lem7027826 A s)). Qed.
Lemma lem7027832 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term216 A t s) : term216 A t s.
Proof. exact (h1). Qed.
Lemma lem7027833 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term216 A t s) : term554 A t s.
Proof. exact (fun h0 : @IN (A -> Prop) t s => @lem7027832 A t s h1). Qed.
Lemma lem7027835 (p : Prop) : (term377 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7027836 {A : Type'} (t : A -> Prop) (s : type686 A) : (term554 A t s) = (term216 A t s).
Proof. exact (@lem7027835 (@IN (A -> Prop) t s)). Qed.
Lemma lem7027837 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term216 A t s) : term216 A t s.
Proof. exact (EQ_MP (@lem7027836 A t s) (@lem7027833 A t s h1)). Qed.
Lemma lem7027839 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term531 A t s x t') : @IN (A -> Prop) t' s.
Proof. exact (proj1 (@lem7027412 A t s x t' h1)). Qed.
Lemma lem7027840 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term531 A t s x t') : term373 A t' s.
Proof. exact (fun h0 : term216 A t' s => @lem7027839 A t s x t' h1). Qed.
Lemma lem7027842 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7027843 {A : Type'} (t' : A -> Prop) (s : type686 A) : (term373 A t' s) = (@IN (A -> Prop) t' s).
Proof. exact (@lem7027842 (@IN (A -> Prop) t' s)). Qed.
Lemma lem7027844 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term531 A t s x t') : @IN (A -> Prop) t' s.
Proof. exact (EQ_MP (@lem7027843 A t' s) (@lem7027840 A t s x t' h1)). Qed.
Lemma lem7027846 (b : Prop) (a : Prop) : (a \/ b) = (term410 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7027847 {A : Type'} (_93878 : type686 A) (_93876 : type686 A) (_93875 : A -> Prop) (_93877 : A -> Prop) : (term549 A _93877 _93878 _93875 _93876) = (term555 A _93878 _93876 _93875 _93877).
Proof. exact (@lem7027846 (term547 A _93877 _93878 _93875 _93876) (term303 A _93875 _93877)). Qed.
Lemma lem7027849 (a : Prop) (b : Prop) : (term412 a b) = (term413 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7027850 {A : Type'} (_93877 : A -> Prop) (_93878 : type686 A) (_93875 : A -> Prop) (_93876 : type686 A) : (term556 A _93877 _93878 _93875 _93876) = (term557 A _93877 _93878 _93875 _93876).
Proof. exact (@lem7027849 (term558 A _93876 _93878) (term544 A _93877 _93878 _93875 _93876)). Qed.
Lemma lem7027852 (a : Prop) : (term268 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7027853 {A : Type'} (_93876 : type686 A) (_93878 : type686 A) : (term559 A _93876 _93878) = (_93876 = _93878).
Proof. exact (@lem7027852 (_93876 = _93878)). Qed.
Lemma lem7027854 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7027855 {A : Type'} (_93876 : type686 A) (_93878 : type686 A) : (term560 A _93876 _93878) = (term561 A _93876 _93878).
Proof. exact (MK_COMB (@lem7027854) (@lem7027853 A _93876 _93878)). Qed.
Lemma lem7027857 (a : Prop) (b : Prop) : (term412 a b) = (term413 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7027858 {A : Type'} (_93877 : A -> Prop) (_93878 : type686 A) (_93875 : A -> Prop) (_93876 : type686 A) : (term562 A _93877 _93878 _93875 _93876) = (term563 A _93877 _93878 _93875 _93876).
Proof. exact (@lem7027857 (@IN (A -> Prop) _93877 _93878) (term216 A _93875 _93876)). Qed.
Lemma lem7027860 (a : Prop) : (term268 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7027861 {A : Type'} (_93875 : A -> Prop) (_93876 : type686 A) : (term416 A _93875 _93876) = (@IN (A -> Prop) _93875 _93876).
Proof. exact (@lem7027860 (@IN (A -> Prop) _93875 _93876)). Qed.
Lemma lem7027862 {A : Type'} (_93877 : A -> Prop) (_93878 : type686 A) : (term564 A _93877 _93878) = (term564 A _93877 _93878).
Proof. exact (eq_refl (term564 A _93877 _93878)). Qed.
Lemma lem7027863 {A : Type'} (_93877 : A -> Prop) (_93878 : type686 A) (_93875 : A -> Prop) (_93876 : type686 A) : (term563 A _93877 _93878 _93875 _93876) = (term565 A _93877 _93878 _93875 _93876).
Proof. exact (MK_COMB (@lem7027862 A _93877 _93878) (@lem7027861 A _93875 _93876)). Qed.
Lemma lem7027864 {A : Type'} (_93877 : A -> Prop) (_93878 : type686 A) (_93875 : A -> Prop) (_93876 : type686 A) : (term562 A _93877 _93878 _93875 _93876) = (term565 A _93877 _93878 _93875 _93876).
Proof. exact (TRANS (@lem7027858 A _93877 _93878 _93875 _93876) (@lem7027863 A _93877 _93878 _93875 _93876)). Qed.
Lemma lem7027865 {A : Type'} (_93877 : A -> Prop) (_93878 : type686 A) (_93875 : A -> Prop) (_93876 : type686 A) : (term557 A _93877 _93878 _93875 _93876) = (term566 A _93877 _93878 _93875 _93876).
Proof. exact (MK_COMB (@lem7027855 A _93876 _93878) (@lem7027864 A _93877 _93878 _93875 _93876)). Qed.
Lemma lem7027866 {A : Type'} (_93877 : A -> Prop) (_93878 : type686 A) (_93875 : A -> Prop) (_93876 : type686 A) : (term556 A _93877 _93878 _93875 _93876) = (term566 A _93877 _93878 _93875 _93876).
Proof. exact (TRANS (@lem7027850 A _93877 _93878 _93875 _93876) (@lem7027865 A _93877 _93878 _93875 _93876)). Qed.
Lemma lem7027867 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7027868 {A : Type'} (_93877 : A -> Prop) (_93878 : type686 A) (_93875 : A -> Prop) (_93876 : type686 A) : (term567 A _93877 _93878 _93875 _93876) = (term568 A _93877 _93878 _93875 _93876).
Proof. exact (MK_COMB (@lem7027867) (@lem7027866 A _93877 _93878 _93875 _93876)). Qed.
Lemma lem7027869 {A : Type'} (_93875 : A -> Prop) (_93877 : A -> Prop) : (term303 A _93875 _93877) = (term303 A _93875 _93877).
Proof. exact (eq_refl (term303 A _93875 _93877)). Qed.
Lemma lem7027870 {A : Type'} (_93878 : type686 A) (_93876 : type686 A) (_93875 : A -> Prop) (_93877 : A -> Prop) : (term555 A _93878 _93876 _93875 _93877) = (term569 A _93878 _93876 _93875 _93877).
Proof. exact (MK_COMB (@lem7027868 A _93877 _93878 _93875 _93876) (@lem7027869 A _93875 _93877)). Qed.
Lemma lem7027871 {A : Type'} (_93878 : type686 A) (_93876 : type686 A) (_93875 : A -> Prop) (_93877 : A -> Prop) : (term549 A _93877 _93878 _93875 _93876) = (term569 A _93878 _93876 _93875 _93877).
Proof. exact (TRANS (@lem7027847 A _93878 _93876 _93875 _93877) (@lem7027870 A _93878 _93876 _93875 _93877)). Qed.
Lemma lem7027873 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term216 A t s) (h2 : term531 A t s x t') : term570 A t t' s.
Proof. exact (conj (@lem7027837 A t s h1) (@lem7027844 A t s x t' h2)). Qed.
Lemma lem7027874 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term216 A t s) (h2 : term531 A t s x t') : term571 A t t' s.
Proof. exact (conj (@lem7027830 A s) (@lem7027873 A t s x t' h1 h2)). Qed.
Lemma lem7027876 {A : Type'} (_93878 : type686 A) (_93876 : type686 A) (_93875 : A -> Prop) (_93877 : A -> Prop) : term569 A _93878 _93876 _93875 _93877.
Proof. exact (EQ_MP (@lem7027871 A _93878 _93876 _93875 _93877) (@lem7027781 A _93877 _93878 _93875 _93876)). Qed.
Lemma lem7027877 {A : Type'} (_93878 : type686 A) (_93876 : type686 A) (_93875 : A -> Prop) (_93877 : A -> Prop) : term569 A _93878 _93876 _93875 _93877.
Proof. exact (@lem7027876 A _93878 _93876 _93875 _93877). Qed.
Lemma lem7027878 {A : Type'} (s : type686 A) (t' : A -> Prop) (t : A -> Prop) : term572 A s t' t.
Proof. exact (@lem7027877 A s s t' t). Qed.
Lemma lem7027881 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term216 A t s) (h2 : term531 A t s x t') : term303 A t' t.
Proof. exact (@lem7027878 A s t' t (@lem7027874 A t s x t' h1 h2)). Qed.
Lemma lem7027882 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term216 A t s) (h2 : term531 A t s x t') : term573 A t' t.
Proof. exact (fun h0 : t' = t => @lem7027881 A t s x t' h1 h2). Qed.
Lemma lem7027884 (p : Prop) : (term377 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7027885 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term573 A t' t) = (term303 A t' t).
Proof. exact (@lem7027884 (t' = t)). Qed.
Lemma lem7027886 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term216 A t s) (h2 : term531 A t s x t') : term303 A t' t.
Proof. exact (EQ_MP (@lem7027885 A t' t) (@lem7027882 A t s x t' h1 h2)). Qed.
Lemma lem7027888 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term531 A t s x t') : @IN A x t'.
Proof. exact (proj2 (@lem7027412 A t s x t' h1)). Qed.
Lemma lem7027889 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term531 A t s x t') : term375 A x t'.
Proof. exact (fun h0 : term368 A x t' => @lem7027888 A t s x t' h1). Qed.
Lemma lem7027891 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7027892 {A : Type'} (x : A) (t' : A -> Prop) : (term375 A x t') = (@IN A x t').
Proof. exact (@lem7027891 (@IN A x t')). Qed.
Lemma lem7027893 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term531 A t s x t') : @IN A x t'.
Proof. exact (EQ_MP (@lem7027892 A x t') (@lem7027889 A t s x t' h1)). Qed.
Lemma lem7027895 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term531 A t s x t') : @IN A x t.
Proof. exact (proj1 (@lem7027411 A t s x t' h1)). Qed.
Lemma lem7027896 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term531 A t s x t') : term375 A x t.
Proof. exact (fun h0 : term368 A x t => @lem7027895 A t s x t' h1). Qed.
Lemma lem7027898 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7027899 {A : Type'} (x : A) (t : A -> Prop) : (term375 A x t) = (@IN A x t).
Proof. exact (@lem7027898 (@IN A x t)). Qed.
Lemma lem7027900 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term531 A t s x t') : @IN A x t.
Proof. exact (EQ_MP (@lem7027899 A x t) (@lem7027896 A t s x t' h1)). Qed.
Lemma lem7027906 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7027907 {A : Type'} (t : A -> Prop) (s : type686 A) (_93864 : A -> Prop) (_93865 : A -> Prop) (f : A -> nat) (_93866 : A) : (term541 A s t _93864 _93865 f _93866) = (term574 A t s _93864 _93865 f _93866).
Proof. exact (@lem7027906 (term303 A _93865 t) (term216 A _93864 s) (term369 A _93864 _93865 f _93866)). Qed.
Lemma lem7027923 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7027924 {A : Type'} (s : type686 A) (_93864 : A -> Prop) (_93865 : A -> Prop) (f : A -> nat) (_93866 : A) : (term575 A s _93864 _93865 f _93866) = (term576 A s _93864 _93865 f _93866).
Proof. exact (@lem7027923 (_93864 = _93865) (term216 A _93864 s) (term367 A _93864 _93865 f _93866)). Qed.
Lemma lem7027940 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7027941 {A : Type'} (_93864 : A -> Prop) (s : type686 A) (_93865 : A -> Prop) (f : A -> nat) (_93866 : A) : (term577 A s _93864 _93865 f _93866) = (term578 A _93864 s _93865 f _93866).
Proof. exact (@lem7027940 (term368 A _93866 _93864) (term216 A _93864 s) (term381 A _93865 f _93866)). Qed.
Lemma lem7027955 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7027956 {A : Type'} (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) (f : A -> nat) (_93866 : A) : (term579 A _93864 s _93865 f _93866) = (term580 A _93865 _93864 s f _93866).
Proof. exact (@lem7027955 (term368 A _93866 _93865) (term216 A _93864 s) ((f _93866) = (NUMERAL 0))). Qed.
Lemma lem7027970 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7027971 {A : Type'} (f : A -> nat) (_93866 : A) (_93864 : A -> Prop) (s : type686 A) : (term384 A _93864 s f _93866) = (term385 A f _93866 _93864 s).
Proof. exact (@lem7027970 ((f _93866) = (NUMERAL 0)) (term216 A _93864 s)). Qed.
Lemma lem7027979 {A : Type'} (_93866 : A) (_93865 : A -> Prop) : (term386 A _93866 _93865) = (term386 A _93866 _93865).
Proof. exact (eq_refl (term386 A _93866 _93865)). Qed.
Lemma lem7027980 {A : Type'} (_93865 : A -> Prop) (f : A -> nat) (_93866 : A) (_93864 : A -> Prop) (s : type686 A) : (term580 A _93865 _93864 s f _93866) = (term581 A _93865 f _93866 _93864 s).
Proof. exact (MK_COMB (@lem7027979 A _93866 _93865) (@lem7027971 A f _93866 _93864 s)). Qed.
Lemma lem7027984 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7027985 {A : Type'} (f : A -> nat) (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term581 A _93865 f _93866 _93864 s) = (term582 A f _93866 _93865 _93864 s).
Proof. exact (@lem7027984 ((f _93866) = (NUMERAL 0)) (term368 A _93866 _93865) (term216 A _93864 s)). Qed.
Lemma lem7028003 {A : Type'} (f : A -> nat) (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term580 A _93865 _93864 s f _93866) = (term582 A f _93866 _93865 _93864 s).
Proof. exact (TRANS (@lem7027980 A _93865 f _93866 _93864 s) (@lem7027985 A f _93866 _93865 _93864 s)). Qed.
Lemma lem7028004 {A : Type'} (f : A -> nat) (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term579 A _93864 s _93865 f _93866) = (term582 A f _93866 _93865 _93864 s).
Proof. exact (TRANS (@lem7027956 A _93865 _93864 s f _93866) (@lem7028003 A f _93866 _93865 _93864 s)). Qed.
Lemma lem7028005 {A : Type'} (_93866 : A) (_93864 : A -> Prop) : (term386 A _93866 _93864) = (term386 A _93866 _93864).
Proof. exact (eq_refl (term386 A _93866 _93864)). Qed.
Lemma lem7028006 {A : Type'} (f : A -> nat) (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term578 A _93864 s _93865 f _93866) = (term583 A f _93866 _93865 _93864 s).
Proof. exact (MK_COMB (@lem7028005 A _93866 _93864) (@lem7028004 A f _93866 _93865 _93864 s)). Qed.
Lemma lem7028010 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7028011 {A : Type'} (f : A -> nat) (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term583 A f _93866 _93865 _93864 s) = (term584 A f _93866 _93865 _93864 s).
Proof. exact (@lem7028010 ((f _93866) = (NUMERAL 0)) (term368 A _93866 _93864) (term585 A _93866 _93865 _93864 s)). Qed.
Lemma lem7028039 {A : Type'} (f : A -> nat) (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term578 A _93864 s _93865 f _93866) = (term584 A f _93866 _93865 _93864 s).
Proof. exact (TRANS (@lem7028006 A f _93866 _93865 _93864 s) (@lem7028011 A f _93866 _93865 _93864 s)). Qed.
Lemma lem7028040 {A : Type'} (f : A -> nat) (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term577 A s _93864 _93865 f _93866) = (term584 A f _93866 _93865 _93864 s).
Proof. exact (TRANS (@lem7027941 A _93864 s _93865 f _93866) (@lem7028039 A f _93866 _93865 _93864 s)). Qed.
Lemma lem7028041 {A : Type'} (_93864 : A -> Prop) (_93865 : A -> Prop) : (term187 A _93864 _93865) = (term187 A _93864 _93865).
Proof. exact (eq_refl (term187 A _93864 _93865)). Qed.
Lemma lem7028042 {A : Type'} (f : A -> nat) (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term576 A s _93864 _93865 f _93866) = (term586 A f _93866 _93865 _93864 s).
Proof. exact (MK_COMB (@lem7028041 A _93864 _93865) (@lem7028040 A f _93866 _93865 _93864 s)). Qed.
Lemma lem7028053 {A : Type'} (f : A -> nat) (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term575 A s _93864 _93865 f _93866) = (term586 A f _93866 _93865 _93864 s).
Proof. exact (TRANS (@lem7027924 A s _93864 _93865 f _93866) (@lem7028042 A f _93866 _93865 _93864 s)). Qed.
Lemma lem7028054 {A : Type'} (_93865 : A -> Prop) (t : A -> Prop) : (term539 A _93865 t) = (term539 A _93865 t).
Proof. exact (eq_refl (term539 A _93865 t)). Qed.
Lemma lem7028055 {A : Type'} (t : A -> Prop) (f : A -> nat) (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term574 A t s _93864 _93865 f _93866) = (term587 A t f _93866 _93865 _93864 s).
Proof. exact (MK_COMB (@lem7028054 A _93865 t) (@lem7028053 A f _93866 _93865 _93864 s)). Qed.
Lemma lem7028059 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7028060 {A : Type'} (t : A -> Prop) (f : A -> nat) (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term587 A t f _93866 _93865 _93864 s) = (term588 A t f _93866 _93865 _93864 s).
Proof. exact (@lem7028059 (_93864 = _93865) (term303 A _93865 t) (term584 A f _93866 _93865 _93864 s)). Qed.
Lemma lem7028076 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7028077 {A : Type'} (f : A -> nat) (t : A -> Prop) (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term589 A t f _93866 _93865 _93864 s) = (term590 A f t _93866 _93865 _93864 s).
Proof. exact (@lem7028076 ((f _93866) = (NUMERAL 0)) (term303 A _93865 t) (term591 A _93866 _93865 _93864 s)). Qed.
Lemma lem7028117 {A : Type'} (_93864 : A -> Prop) (_93865 : A -> Prop) : (term187 A _93864 _93865) = (term187 A _93864 _93865).
Proof. exact (eq_refl (term187 A _93864 _93865)). Qed.
Lemma lem7028118 {A : Type'} (f : A -> nat) (t : A -> Prop) (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term588 A t f _93866 _93865 _93864 s) = (term592 A f t _93866 _93865 _93864 s).
Proof. exact (MK_COMB (@lem7028117 A _93864 _93865) (@lem7028077 A f t _93866 _93865 _93864 s)). Qed.
Lemma lem7028129 {A : Type'} (f : A -> nat) (t : A -> Prop) (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term587 A t f _93866 _93865 _93864 s) = (term592 A f t _93866 _93865 _93864 s).
Proof. exact (TRANS (@lem7028060 A t f _93866 _93865 _93864 s) (@lem7028118 A f t _93866 _93865 _93864 s)). Qed.
Lemma lem7028130 {A : Type'} (f : A -> nat) (t : A -> Prop) (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term574 A t s _93864 _93865 f _93866) = (term592 A f t _93866 _93865 _93864 s).
Proof. exact (TRANS (@lem7028055 A t f _93866 _93865 _93864 s) (@lem7028129 A f t _93866 _93865 _93864 s)). Qed.
Lemma lem7028131 {A : Type'} (f : A -> nat) (t : A -> Prop) (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term541 A s t _93864 _93865 f _93866) = (term592 A f t _93866 _93865 _93864 s).
Proof. exact (TRANS (@lem7027907 A t s _93864 _93865 f _93866) (@lem7028130 A f t _93866 _93865 _93864 s)). Qed.
Lemma lem7028132 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7028133 {A : Type'} (f : A -> nat) (t : A -> Prop) (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term593 A s t _93864 _93865 f _93866) = (term594 A f t _93866 _93865 _93864 s).
Proof. exact (MK_COMB (@lem7028132) (@lem7028131 A f t _93866 _93865 _93864 s)). Qed.
Lemma lem7028149 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7028150 {A : Type'} (t : A -> Prop) (s : type686 A) (_93864 : A -> Prop) (_93866 : A) (_93865 : A -> Prop) : (term347 A s t _93864 _93866 _93865) = (term595 A t s _93864 _93866 _93865).
Proof. exact (@lem7028149 (term303 A _93865 t) (term216 A _93864 s) (term301 A _93864 _93866 _93865)). Qed.
Lemma lem7028166 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7028167 {A : Type'} (s : type686 A) (_93864 : A -> Prop) (_93866 : A) (_93865 : A -> Prop) : (term596 A s _93864 _93866 _93865) = (term597 A s _93864 _93866 _93865).
Proof. exact (@lem7028166 (_93864 = _93865) (term216 A _93864 s) (term298 A _93864 _93866 _93865)). Qed.
Lemma lem7028183 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7028184 {A : Type'} (_93864 : A -> Prop) (s : type686 A) (_93866 : A) (_93865 : A -> Prop) : (term598 A s _93864 _93866 _93865) = (term599 A _93864 s _93866 _93865).
Proof. exact (@lem7028183 (term368 A _93866 _93864) (term216 A _93864 s) (term368 A _93866 _93865)). Qed.
Lemma lem7028198 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7028199 {A : Type'} (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term600 A _93864 s _93866 _93865) = (term585 A _93866 _93865 _93864 s).
Proof. exact (@lem7028198 (term368 A _93866 _93865) (term216 A _93864 s)). Qed.
Lemma lem7028205 {A : Type'} (_93866 : A) (_93864 : A -> Prop) : (term386 A _93866 _93864) = (term386 A _93866 _93864).
Proof. exact (eq_refl (term386 A _93866 _93864)). Qed.
Lemma lem7028206 {A : Type'} (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term599 A _93864 s _93866 _93865) = (term591 A _93866 _93865 _93864 s).
Proof. exact (MK_COMB (@lem7028205 A _93866 _93864) (@lem7028199 A _93866 _93865 _93864 s)). Qed.
Lemma lem7028217 {A : Type'} (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term598 A s _93864 _93866 _93865) = (term591 A _93866 _93865 _93864 s).
Proof. exact (TRANS (@lem7028184 A _93864 s _93866 _93865) (@lem7028206 A _93866 _93865 _93864 s)). Qed.
Lemma lem7028218 {A : Type'} (_93864 : A -> Prop) (_93865 : A -> Prop) : (term187 A _93864 _93865) = (term187 A _93864 _93865).
Proof. exact (eq_refl (term187 A _93864 _93865)). Qed.
Lemma lem7028219 {A : Type'} (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term597 A s _93864 _93866 _93865) = (term601 A _93866 _93865 _93864 s).
Proof. exact (MK_COMB (@lem7028218 A _93864 _93865) (@lem7028217 A _93866 _93865 _93864 s)). Qed.
Lemma lem7028230 {A : Type'} (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term596 A s _93864 _93866 _93865) = (term601 A _93866 _93865 _93864 s).
Proof. exact (TRANS (@lem7028167 A s _93864 _93866 _93865) (@lem7028219 A _93866 _93865 _93864 s)). Qed.
Lemma lem7028231 {A : Type'} (_93865 : A -> Prop) (t : A -> Prop) : (term539 A _93865 t) = (term539 A _93865 t).
Proof. exact (eq_refl (term539 A _93865 t)). Qed.
Lemma lem7028232 {A : Type'} (t : A -> Prop) (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term595 A t s _93864 _93866 _93865) = (term602 A t _93866 _93865 _93864 s).
Proof. exact (MK_COMB (@lem7028231 A _93865 t) (@lem7028230 A _93866 _93865 _93864 s)). Qed.
Lemma lem7028236 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7028237 {A : Type'} (t : A -> Prop) (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term602 A t _93866 _93865 _93864 s) = (term603 A t _93866 _93865 _93864 s).
Proof. exact (@lem7028236 (_93864 = _93865) (term303 A _93865 t) (term591 A _93866 _93865 _93864 s)). Qed.
Lemma lem7028277 {A : Type'} (t : A -> Prop) (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term595 A t s _93864 _93866 _93865) = (term603 A t _93866 _93865 _93864 s).
Proof. exact (TRANS (@lem7028232 A t _93866 _93865 _93864 s) (@lem7028237 A t _93866 _93865 _93864 s)). Qed.
Lemma lem7028278 {A : Type'} (t : A -> Prop) (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term347 A s t _93864 _93866 _93865) = (term603 A t _93866 _93865 _93864 s).
Proof. exact (TRANS (@lem7028150 A t s _93864 _93866 _93865) (@lem7028277 A t _93866 _93865 _93864 s)). Qed.
Lemma lem7028279 {A : Type'} (f : A -> nat) (_93866 : A) : (term403 A f _93866) = (term403 A f _93866).
Proof. exact (eq_refl (term403 A f _93866)). Qed.
Lemma lem7028280 {A : Type'} (f : A -> nat) (t : A -> Prop) (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term604 A f s t _93864 _93866 _93865) = (term605 A f t _93866 _93865 _93864 s).
Proof. exact (MK_COMB (@lem7028279 A f _93866) (@lem7028278 A t _93866 _93865 _93864 s)). Qed.
Lemma lem7028284 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7028285 {A : Type'} (f : A -> nat) (t : A -> Prop) (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term605 A f t _93866 _93865 _93864 s) = (term592 A f t _93866 _93865 _93864 s).
Proof. exact (@lem7028284 (_93864 = _93865) ((f _93866) = (NUMERAL 0)) (term606 A t _93866 _93865 _93864 s)). Qed.
Lemma lem7028337 {A : Type'} (f : A -> nat) (t : A -> Prop) (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : (term604 A f s t _93864 _93866 _93865) = (term592 A f t _93866 _93865 _93864 s).
Proof. exact (TRANS (@lem7028280 A f t _93866 _93865 _93864 s) (@lem7028285 A f t _93866 _93865 _93864 s)). Qed.
Lemma lem7028338 {A : Type'} (f : A -> nat) (t : A -> Prop) (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : ((term541 A s t _93864 _93865 f _93866) = (term604 A f s t _93864 _93866 _93865)) = ((term592 A f t _93866 _93865 _93864 s) = (term592 A f t _93866 _93865 _93864 s)).
Proof. exact (MK_COMB (@lem7028133 A f t _93866 _93865 _93864 s) (@lem7028337 A f t _93866 _93865 _93864 s)). Qed.
Lemma lem7028340 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7028341 (x : Prop) : (x = x) = True.
Proof. exact (@lem7028340 Prop x). Qed.
Lemma lem7028342 {A : Type'} (f : A -> nat) (t : A -> Prop) (_93866 : A) (_93865 : A -> Prop) (_93864 : A -> Prop) (s : type686 A) : ((term592 A f t _93866 _93865 _93864 s) = (term592 A f t _93866 _93865 _93864 s)) = True.
Proof. exact (@lem7028341 (term592 A f t _93866 _93865 _93864 s)). Qed.
Lemma lem7028343 {A : Type'} (f : A -> nat) (s : type686 A) (t : A -> Prop) (_93864 : A -> Prop) (_93866 : A) (_93865 : A -> Prop) : ((term541 A s t _93864 _93865 f _93866) = (term604 A f s t _93864 _93866 _93865)) = True.
Proof. exact (TRANS (@lem7028338 A f t _93866 _93865 _93864 s) (@lem7028342 A f t _93866 _93865 _93864 s)). Qed.
Lemma lem7028344 {A : Type'} (f : A -> nat) (s : type686 A) (t : A -> Prop) (_93864 : A -> Prop) (_93866 : A) (_93865 : A -> Prop) : True = ((term541 A s t _93864 _93865 f _93866) = (term604 A f s t _93864 _93866 _93865)).
Proof. exact (SYM (@lem7028343 A f s t _93864 _93866 _93865)). Qed.
Lemma lem7028345 {A : Type'} (f : A -> nat) (s : type686 A) (t : A -> Prop) (_93864 : A -> Prop) (_93866 : A) (_93865 : A -> Prop) : (term541 A s t _93864 _93865 f _93866) = (term604 A f s t _93864 _93866 _93865).
Proof. exact (EQ_MP (@lem7028344 A f s t _93864 _93866 _93865) (@lem0)). Qed.
Lemma lem7028346 {A : Type'} (_93864 : A -> Prop) (_93866 : A) (_93865 : A -> Prop) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term604 A f s t _93864 _93866 _93865.
Proof. exact (EQ_MP (@lem7028345 A f s t _93864 _93866 _93865) (@lem7027707 A _93864 _93865 _93866 t s f h1)). Qed.
Lemma lem7028348 (b : Prop) (a : Prop) : (a \/ b) = (term410 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7028349 {A : Type'} (s : type686 A) (t : A -> Prop) (_93864 : A -> Prop) (_93865 : A -> Prop) (f : A -> nat) (_93866 : A) : (term604 A f s t _93864 _93866 _93865) = (term607 A s t _93864 _93865 f _93866).
Proof. exact (@lem7028348 (term347 A s t _93864 _93866 _93865) ((f _93866) = (NUMERAL 0))). Qed.
Lemma lem7028351 (a : Prop) (b : Prop) : (term412 a b) = (term413 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7028352 {A : Type'} (s : type686 A) (t : A -> Prop) (_93864 : A -> Prop) (_93866 : A) (_93865 : A -> Prop) : (term608 A s t _93864 _93866 _93865) = (term609 A s t _93864 _93866 _93865).
Proof. exact (@lem7028351 (term216 A _93864 s) (term328 A t _93864 _93866 _93865)). Qed.
Lemma lem7028354 (a : Prop) : (term268 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7028355 {A : Type'} (_93864 : A -> Prop) (s : type686 A) : (term416 A _93864 s) = (@IN (A -> Prop) _93864 s).
Proof. exact (@lem7028354 (@IN (A -> Prop) _93864 s)). Qed.
Lemma lem7028356 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7028357 {A : Type'} (_93864 : A -> Prop) (s : type686 A) : (term417 A _93864 s) = (term418 A _93864 s).
Proof. exact (MK_COMB (@lem7028356) (@lem7028355 A _93864 s)). Qed.
Lemma lem7028359 (a : Prop) (b : Prop) : (term412 a b) = (term413 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7028360 {A : Type'} (t : A -> Prop) (_93864 : A -> Prop) (_93866 : A) (_93865 : A -> Prop) : (term610 A t _93864 _93866 _93865) = (term611 A t _93864 _93866 _93865).
Proof. exact (@lem7028359 (term303 A _93865 t) (term301 A _93864 _93866 _93865)). Qed.
Lemma lem7028362 (a : Prop) : (term268 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7028363 {A : Type'} (_93865 : A -> Prop) (t : A -> Prop) : (term296 A _93865 t) = (_93865 = t).
Proof. exact (@lem7028362 (_93865 = t)). Qed.
Lemma lem7028364 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7028365 {A : Type'} (_93865 : A -> Prop) (t : A -> Prop) : (term612 A _93865 t) = (term613 A _93865 t).
Proof. exact (MK_COMB (@lem7028364) (@lem7028363 A _93865 t)). Qed.
Lemma lem7028367 (a : Prop) (b : Prop) : (term412 a b) = (term413 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7028368 {A : Type'} (_93864 : A -> Prop) (_93866 : A) (_93865 : A -> Prop) : (term614 A _93864 _93866 _93865) = (term615 A _93864 _93866 _93865).
Proof. exact (@lem7028367 (_93864 = _93865) (term298 A _93864 _93866 _93865)). Qed.
Lemma lem7028370 (a : Prop) (b : Prop) : (term412 a b) = (term413 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7028371 {A : Type'} (_93864 : A -> Prop) (_93866 : A) (_93865 : A -> Prop) : (term616 A _93864 _93866 _93865) = (term617 A _93864 _93866 _93865).
Proof. exact (@lem7028370 (term368 A _93866 _93864) (term368 A _93866 _93865)). Qed.
Lemma lem7028373 (a : Prop) : (term268 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7028374 {A : Type'} (_93866 : A) (_93864 : A -> Prop) : (term423 A _93866 _93864) = (@IN A _93866 _93864).
Proof. exact (@lem7028373 (@IN A _93866 _93864)). Qed.
Lemma lem7028375 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7028376 {A : Type'} (_93866 : A) (_93864 : A -> Prop) : (term424 A _93866 _93864) = (term425 A _93866 _93864).
Proof. exact (MK_COMB (@lem7028375) (@lem7028374 A _93866 _93864)). Qed.
Lemma lem7028378 (a : Prop) : (term268 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7028379 {A : Type'} (_93866 : A) (_93865 : A -> Prop) : (term423 A _93866 _93865) = (@IN A _93866 _93865).
Proof. exact (@lem7028378 (@IN A _93866 _93865)). Qed.
Lemma lem7028380 {A : Type'} (_93864 : A -> Prop) (_93866 : A) (_93865 : A -> Prop) : (term617 A _93864 _93866 _93865) = (term304 A _93864 _93866 _93865).
Proof. exact (MK_COMB (@lem7028376 A _93866 _93864) (@lem7028379 A _93866 _93865)). Qed.
Lemma lem7028381 {A : Type'} (_93864 : A -> Prop) (_93866 : A) (_93865 : A -> Prop) : (term616 A _93864 _93866 _93865) = (term304 A _93864 _93866 _93865).
Proof. exact (TRANS (@lem7028371 A _93864 _93866 _93865) (@lem7028380 A _93864 _93866 _93865)). Qed.
Lemma lem7028382 {A : Type'} (_93864 : A -> Prop) (_93865 : A -> Prop) : (term618 A _93864 _93865) = (term618 A _93864 _93865).
Proof. exact (eq_refl (term618 A _93864 _93865)). Qed.
Lemma lem7028383 {A : Type'} (_93864 : A -> Prop) (_93866 : A) (_93865 : A -> Prop) : (term615 A _93864 _93866 _93865) = (term112 A _93864 _93866 _93865).
Proof. exact (MK_COMB (@lem7028382 A _93864 _93865) (@lem7028381 A _93864 _93866 _93865)). Qed.
Lemma lem7028384 {A : Type'} (_93864 : A -> Prop) (_93866 : A) (_93865 : A -> Prop) : (term614 A _93864 _93866 _93865) = (term112 A _93864 _93866 _93865).
Proof. exact (TRANS (@lem7028368 A _93864 _93866 _93865) (@lem7028383 A _93864 _93866 _93865)). Qed.
Lemma lem7028385 {A : Type'} (t : A -> Prop) (_93864 : A -> Prop) (_93866 : A) (_93865 : A -> Prop) : (term611 A t _93864 _93866 _93865) = (term619 A t _93864 _93866 _93865).
Proof. exact (MK_COMB (@lem7028365 A _93865 t) (@lem7028384 A _93864 _93866 _93865)). Qed.
Lemma lem7028386 {A : Type'} (t : A -> Prop) (_93864 : A -> Prop) (_93866 : A) (_93865 : A -> Prop) : (term610 A t _93864 _93866 _93865) = (term619 A t _93864 _93866 _93865).
Proof. exact (TRANS (@lem7028360 A t _93864 _93866 _93865) (@lem7028385 A t _93864 _93866 _93865)). Qed.
Lemma lem7028387 {A : Type'} (s : type686 A) (t : A -> Prop) (_93864 : A -> Prop) (_93866 : A) (_93865 : A -> Prop) : (term609 A s t _93864 _93866 _93865) = (term620 A s t _93864 _93866 _93865).
Proof. exact (MK_COMB (@lem7028357 A _93864 s) (@lem7028386 A t _93864 _93866 _93865)). Qed.
Lemma lem7028388 {A : Type'} (s : type686 A) (t : A -> Prop) (_93864 : A -> Prop) (_93866 : A) (_93865 : A -> Prop) : (term608 A s t _93864 _93866 _93865) = (term620 A s t _93864 _93866 _93865).
Proof. exact (TRANS (@lem7028352 A s t _93864 _93866 _93865) (@lem7028387 A s t _93864 _93866 _93865)). Qed.
Lemma lem7028389 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7028390 {A : Type'} (s : type686 A) (t : A -> Prop) (_93864 : A -> Prop) (_93866 : A) (_93865 : A -> Prop) : (term621 A s t _93864 _93866 _93865) = (term622 A s t _93864 _93866 _93865).
Proof. exact (MK_COMB (@lem7028389) (@lem7028388 A s t _93864 _93866 _93865)). Qed.
Lemma lem7028391 {A : Type'} (f : A -> nat) (_93866 : A) : ((f _93866) = (NUMERAL 0)) = ((f _93866) = (NUMERAL 0)).
Proof. exact (eq_refl ((f _93866) = (NUMERAL 0))). Qed.
Lemma lem7028392 {A : Type'} (s : type686 A) (t : A -> Prop) (_93864 : A -> Prop) (_93865 : A -> Prop) (f : A -> nat) (_93866 : A) : (term607 A s t _93864 _93865 f _93866) = (term623 A s t _93864 _93865 f _93866).
Proof. exact (MK_COMB (@lem7028390 A s t _93864 _93866 _93865) (@lem7028391 A f _93866)). Qed.
Lemma lem7028393 {A : Type'} (s : type686 A) (t : A -> Prop) (_93864 : A -> Prop) (_93865 : A -> Prop) (f : A -> nat) (_93866 : A) : (term604 A f s t _93864 _93866 _93865) = (term623 A s t _93864 _93865 f _93866).
Proof. exact (TRANS (@lem7028349 A s t _93864 _93865 f _93866) (@lem7028392 A s t _93864 _93865 f _93866)). Qed.
Lemma lem7028395 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term531 A t s x t') : term304 A t' x t.
Proof. exact (conj (@lem7027893 A t s x t' h1) (@lem7027900 A t s x t' h1)). Qed.
Lemma lem7028396 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term216 A t s) (h2 : term531 A t s x t') : term112 A t' x t.
Proof. exact (conj (@lem7027886 A t s x t' h1 h2) (@lem7028395 A t s x t' h2)). Qed.
Lemma lem7028397 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term216 A t s) (h2 : term531 A t s x t') : term624 A t' x t.
Proof. exact (conj (@lem7027821 A t) (@lem7028396 A t s x t' h1 h2)). Qed.
Lemma lem7028398 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term216 A t s) (h2 : term531 A t s x t') : term625 A s t' x t.
Proof. exact (conj (@lem7027812 A t s x t' h2) (@lem7028397 A t s x t' h1 h2)). Qed.
Lemma lem7028400 {A : Type'} (_93864 : A -> Prop) (_93865 : A -> Prop) (_93866 : A) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term623 A s t _93864 _93865 f _93866.
Proof. exact (EQ_MP (@lem7028393 A s t _93864 _93865 f _93866) (@lem7028346 A _93864 _93866 _93865 t s f h1)). Qed.
Lemma lem7028401 {A : Type'} (_93864 : A -> Prop) (_93865 : A -> Prop) (_93866 : A) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term623 A s t _93864 _93865 f _93866.
Proof. exact (@lem7028400 A _93864 _93865 _93866 t s f h1). Qed.
Lemma lem7028402 {A : Type'} (t' : A -> Prop) (x : A) (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term626 A s t' t f x.
Proof. exact (@lem7028401 A t' t x t s f h1). Qed.
Lemma lem7028405 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term132 A t s f) (h2 : term216 A t s) (h3 : term531 A t s x t') : (f x) = (NUMERAL 0).
Proof. exact (@lem7028402 A t' x t s f h1 (@lem7028398 A t s x t' h2 h3)). Qed.
Lemma lem7028406 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term132 A t s f) (h2 : term216 A t s) (h3 : term531 A t s x t') : term627 A f x.
Proof. exact (fun h0 : term293 A f x => @lem7028405 A f t s x t' h1 h2 h3). Qed.
Lemma lem7028408 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7028409 {A : Type'} (f : A -> nat) (x : A) : (term627 A f x) = ((f x) = (NUMERAL 0)).
Proof. exact (@lem7028408 ((f x) = (NUMERAL 0))). Qed.
Lemma lem7028410 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term132 A t s f) (h2 : term216 A t s) (h3 : term531 A t s x t') : (f x) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem7028409 A f x) (@lem7028406 A f t s x t' h1 h2 h3)). Qed.
Lemma lem7028413 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7028415 {A : Type'} (f : A -> nat) (x : A) : (term293 A f x) = (term628 A f x).
Proof. exact (@lem7028413 ((f x) = (NUMERAL 0))). Qed.
Lemma lem7028418 {A : Type'} (f : A -> nat) (x : A) (h1 : term293 A f x) : term628 A f x.
Proof. exact (EQ_MP (@lem7028415 A f x) (@lem7027581 A f x h1)). Qed.
Lemma lem7028421 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term216 A t s) (h4 : term531 A t s x t') : False.
Proof. exact (@lem7028418 A f x h2 (@lem7028410 A f t s x t' h1 h3 h4)). Qed.
Lemma lem7028422 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term216 A t s) (h4 : term531 A t s x t') : term437.
Proof. exact (fun h0 : ~ False => @lem7028421 A f t s x t' h1 h2 h3 h4). Qed.
Lemma lem7028424 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7028425 : term437 = False.
Proof. exact (@lem7028424 False). Qed.
Lemma lem7028426 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term216 A t s) (h4 : term531 A t s x t') : False.
Proof. exact (EQ_MP (@lem7028425) (@lem7028422 A f t s x t' h1 h2 h3 h4)). Qed.
Lemma lem7028427 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term216 A t s) (h4 : term531 A t s x t') : (term293 A f x) = False.
Proof. exact (prop_ext (fun h5 : term293 A f x => @lem7028426 A f t s x t' h1 h2 h3 h4) (fun h5 : False => @lem7027581 A f x h2)). Qed.
Lemma lem7028428 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term216 A t s) (h4 : term531 A t s x t') : False.
Proof. exact (EQ_MP (@lem7028427 A f t s x t' h1 h2 h3 h4) (@lem7027581 A f x h2)). Qed.
Lemma lem7028429 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term216 A t s) (h4 : term531 A t s x t') : (term216 A t s) = False.
Proof. exact (prop_ext (fun h5 : term216 A t s => @lem7028428 A f t s x t' h1 h2 h3 h4) (fun h5 : False => @lem7027577 A t s h3)). Qed.
Lemma lem7028430 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term216 A t s) (h4 : term531 A t s x t') : False.
Proof. exact (EQ_MP (@lem7028429 A f t s x t' h1 h2 h3 h4) (@lem7027577 A t s h3)). Qed.
Lemma lem7028431 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term216 A t s) (h4 : term531 A t s x t') : (term293 A f x) = False.
Proof. exact (prop_ext (fun h5 : term293 A f x => @lem7028430 A f t s x t' h1 h2 h3 h4) (fun h5 : False => @lem7027543 A f x h2)). Qed.
Lemma lem7028432 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term216 A t s) (h4 : term531 A t s x t') : False.
Proof. exact (EQ_MP (@lem7028431 A f t s x t' h1 h2 h3 h4) (@lem7027543 A f x h2)). Qed.
Lemma lem7028433 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term216 A t s) (h4 : term531 A t s x t') : (term216 A t s) = False.
Proof. exact (prop_ext (fun h5 : term216 A t s => @lem7028432 A f t s x t' h1 h2 h3 h4) (fun h5 : False => @lem7027535 A t s h3)). Qed.
Lemma lem7028434 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term216 A t s) (h4 : term531 A t s x t') : False.
Proof. exact (EQ_MP (@lem7028433 A f t s x t' h1 h2 h3 h4) (@lem7027535 A t s h3)). Qed.
Lemma lem7028435 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term216 A t s) (h4 : term531 A t s x t') : (term293 A f x) = False.
Proof. exact (prop_ext (fun h5 : term293 A f x => @lem7028434 A f t s x t' h1 h2 h3 h4) (fun h5 : False => @lem7027543 A f x h2)). Qed.
Lemma lem7028436 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term216 A t s) (h4 : term531 A t s x t') : False.
Proof. exact (EQ_MP (@lem7028435 A f t s x t' h1 h2 h3 h4) (@lem7027543 A f x h2)). Qed.
Lemma lem7028437 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term216 A t s) (h4 : term531 A t s x t') : (term216 A t s) = False.
Proof. exact (prop_ext (fun h5 : term216 A t s => @lem7028436 A f t s x t' h1 h2 h3 h4) (fun h5 : False => @lem7027535 A t s h3)). Qed.
Lemma lem7028438 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term216 A t s) (h4 : term531 A t s x t') : False.
Proof. exact (EQ_MP (@lem7028437 A f t s x t' h1 h2 h3 h4) (@lem7027535 A t s h3)). Qed.
Lemma lem7028439 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term216 A t s) (h4 : term531 A t s x t') : (term531 A t s x t') = False.
Proof. exact (prop_ext (fun h5 : term531 A t s x t' => @lem7028438 A f t s x t' h1 h2 h3 h4) (fun h5 : False => @lem7027411 A t s x t' h4)). Qed.
Lemma lem7028440 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term216 A t s) (h4 : term531 A t s x t') : False.
Proof. exact (EQ_MP (@lem7028439 A f t s x t' h1 h2 h3 h4) (@lem7027411 A t s x t' h4)). Qed.
Lemma lem7028441 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term216 A t s) (h4 : term531 A t s x t') : (term293 A f x) = False.
Proof. exact (prop_ext (fun h5 : term293 A f x => @lem7028440 A f t s x t' h1 h2 h3 h4) (fun h5 : False => @lem7027389 A f x h2)). Qed.
Lemma lem7028442 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term216 A t s) (h4 : term531 A t s x t') : False.
Proof. exact (EQ_MP (@lem7028441 A f t s x t' h1 h2 h3 h4) (@lem7027389 A f x h2)). Qed.
Lemma lem7028443 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term216 A t s) (h4 : term531 A t s x t') : (term216 A t s) = False.
Proof. exact (prop_ext (fun h5 : term216 A t s => @lem7028442 A f t s x t' h1 h2 h3 h4) (fun h5 : False => @lem7027373 A t s h3)). Qed.
Lemma lem7028444 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term216 A t s) (h4 : term531 A t s x t') : False.
Proof. exact (EQ_MP (@lem7028443 A f t s x t' h1 h2 h3 h4) (@lem7027373 A t s h3)). Qed.
Lemma lem7028445 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term216 A t s) (h4 : term475 A t s x) : False.
Proof. exact (ex_elim (@lem7027244 A t s x h4) (fun t' : A -> Prop => fun h0 : term533 A t s x t' => @lem7028444 A f t s x t' h1 h2 h3 h0)). Qed.
Lemma lem7028446 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term216 A t s) (h4 : term475 A t s x) : (term293 A f x) = False.
Proof. exact (prop_ext (fun h5 : term293 A f x => @lem7028445 A f t s x h1 h2 h3 h4) (fun h5 : False => @lem7027250 A f x h2)). Qed.
Lemma lem7028447 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term216 A t s) (h4 : term475 A t s x) : False.
Proof. exact (EQ_MP (@lem7028446 A f t s x h1 h2 h3 h4) (@lem7027250 A f x h2)). Qed.
Lemma lem7028448 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term216 A t s) (h4 : term475 A t s x) : (term216 A t s) = False.
Proof. exact (prop_ext (fun h5 : term216 A t s => @lem7028447 A f t s x h1 h2 h3 h4) (fun h5 : False => @lem7027154 A t s h3)). Qed.
Lemma lem7028449 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term216 A t s) (h4 : term475 A t s x) : False.
Proof. exact (EQ_MP (@lem7028448 A f t s x h1 h2 h3 h4) (@lem7027154 A t s h3)). Qed.
Lemma lem7028450 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term216 A t s) (h4 : term475 A t s x) : (term293 A f x) = False.
Proof. exact (prop_ext (fun h5 : term293 A f x => @lem7028449 A f t s x h1 h2 h3 h4) (fun h5 : False => @lem7026980 A f x h2)). Qed.
Lemma lem7028451 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (h1 : term132 A t s f) (h2 : term293 A f x) (h3 : term216 A t s) (h4 : term475 A t s x) : False.
Proof. exact (EQ_MP (@lem7028450 A f t s x h1 h2 h3 h4) (@lem7026980 A f x h2)). Qed.
Lemma lem7028452 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (h1 : term132 A t s f) (h2 : term216 A t s) (h3 : term475 A t s x) : term292 A f x.
Proof. exact (fun h0 : term293 A f x => @lem7028451 A f t s x h1 h0 h2 h3). Qed.
Lemma lem7028453 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (x : A) (h1 : term132 A t s f) (h2 : term216 A t s) (h3 : term475 A t s x) : (f x) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem7026979 A f x) (@lem7028452 A f t s x h1 h2 h3)). Qed.
Lemma lem7028454 {A : Type'} (x : A) (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term216 A t s) : term481 A t s f x.
Proof. exact (fun h0 : term475 A t s x => @lem7028453 A f t s x h1 h2 h0). Qed.
Lemma lem7028459 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term216 A t s) : term485 A t s f.
Proof. exact (fun x : A => @lem7028454 A x f t s h1 h2). Qed.
Lemma lem7028460 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term216 A t s) : term497 A t s f.
Proof. exact (fun h0 : @FINITE (A -> Prop) s => @lem7028459 A f t s h1 h2). Qed.
Lemma lem7028461 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) : term500 A t s f.
Proof. exact (fun h0 : term216 A t s => @lem7028460 A f t s h1 h0). Qed.
Lemma lem7028462 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : term502 A t s f.
Proof. exact (fun h0 : term132 A t s f => @lem7028461 A t s f h0). Qed.
Lemma lem7028463 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : term503 A t s f.
Proof. exact (fun h0 : term107 A t s => @lem7028462 A t s f). Qed.
Lemma lem7028468 {A : Type'} (s : type686 A) (f : A -> nat) : term507 A s f.
Proof. exact (fun t : A -> Prop => @lem7028463 A t s f). Qed.
Lemma lem7028473 {A : Type'} (f : A -> nat) : term511 A f.
Proof. exact (fun s : type686 A => @lem7028468 A s f). Qed.
Lemma lem7028478 {A : Type'} : term515 A.
Proof. exact (fun f : A -> nat => @lem7028473 A f). Qed.
Lemma lem7028479 {A : Type'} : term514 A.
Proof. exact (EQ_MP (@lem7026970 A) (@lem7028478 A)). Qed.
Lemma lem7028480 {A : Type'} (f : A -> nat) : term629 A f.
Proof. exact (@lem7028479 A f). Qed.
Lemma lem7028481 {A : Type'} (f : A -> nat) : (term629 A f) = (term510 A f).
Proof. exact (eq_refl (term629 A f)). Qed.
Lemma lem7028482 {A : Type'} (f : A -> nat) : term510 A f.
Proof. exact (EQ_MP (@lem7028481 A f) (@lem7028480 A f)). Qed.
Lemma lem7028483 {A : Type'} (f : A -> nat) (s : type686 A) : term630 A f s.
Proof. exact (@lem7028482 A f s). Qed.
Lemma lem7028484 {A : Type'} (s : type686 A) (f : A -> nat) : (term630 A f s) = (term506 A s f).
Proof. exact (eq_refl (term630 A f s)). Qed.
Lemma lem7028485 {A : Type'} (s : type686 A) (f : A -> nat) : term506 A s f.
Proof. exact (EQ_MP (@lem7028484 A s f) (@lem7028483 A f s)). Qed.
Lemma lem7028486 {A : Type'} (s : type686 A) (f : A -> nat) (t : A -> Prop) : term631 A s f t.
Proof. exact (@lem7028485 A s f t). Qed.
Lemma lem7028487 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : (term631 A s f t) = (term491 A t s f).
Proof. exact (eq_refl (term631 A s f t)). Qed.
Lemma lem7028488 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : term491 A t s f.
Proof. exact (EQ_MP (@lem7028487 A t s f) (@lem7028486 A s f t)). Qed.
Lemma lem7028490 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : term491 A t s f.
Proof. exact (@lem7026624 A t s f (@lem7028488 A t s f)). Qed.
Lemma lem7028491 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) : term501 A t s f.
Proof. exact (@lem7028490 A t s f (@lem7025520 A t s h1)). Qed.
Lemma lem7028492 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) : term499 A t s f.
Proof. exact (@lem7028491 A f t s h2 (@lem7025534 A t s f h1)). Qed.
Lemma lem7028493 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) (h3 : term216 A t s) : term496 A t s f.
Proof. exact (@lem7028492 A f t s h1 h2 (@lem7025537 A t s h3)). Qed.
Lemma lem7028494 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) (h3 : @FINITE (A -> Prop) s) (h4 : term216 A t s) : term489 A t s f.
Proof. exact (@lem7028493 A f t s h1 h2 h4 (@lem7025536 A s h3)). Qed.
Lemma lem7028495 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) (h3 : @FINITE (A -> Prop) s) (h4 : term490 A t s f) (h5 : term216 A t s) : False.
Proof. exact (@lem7028494 A f t s h1 h2 h3 h5 (@lem7026608 A t s f h4)). Qed.
Lemma lem7028496 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) (h3 : @FINITE (A -> Prop) s) (h4 : term490 A t s f) (h5 : term216 A t s) : (term490 A t s f) = False.
Proof. exact (prop_ext (fun h6 : term490 A t s f => @lem7028495 A f t s h1 h2 h3 h4 h5) (fun h6 : False => @lem7026608 A t s f h4)). Qed.
Lemma lem7028497 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) (h3 : @FINITE (A -> Prop) s) (h4 : term490 A t s f) (h5 : term216 A t s) : False.
Proof. exact (EQ_MP (@lem7028496 A f t s h1 h2 h3 h4 h5) (@lem7026608 A t s f h4)). Qed.
Lemma lem7028498 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) (h3 : @FINITE (A -> Prop) s) (h4 : term216 A t s) : term489 A t s f.
Proof. exact (fun h0 : term490 A t s f => @lem7028497 A f t s h1 h2 h3 h0 h4). Qed.
Lemma lem7028499 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) (h3 : @FINITE (A -> Prop) s) (h4 : term216 A t s) : term485 A t s f.
Proof. exact (EQ_MP (@lem7026607 A t s f) (@lem7028498 A f t s h1 h2 h3 h4)). Qed.
Lemma lem7028500 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) (h3 : @FINITE (A -> Prop) s) (h4 : term216 A t s) : term488 A t s f.
Proof. exact (EQ_MP (@lem7026603 A f t s h2 h3 h4) (@lem7028499 A f t s h1 h2 h3 h4)). Qed.
Lemma lem7028501 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) (h3 : @FINITE (A -> Prop) s) (h4 : term216 A t s) : (term142 A t s f) = (term632 A t s f).
Proof. exact (@lem7025541 A t s f (@lem7028500 A f t s h1 h2 h3 h4)). Qed.
Lemma lem7028502 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term63 A t s) : @FINITE (A -> Prop) s.
Proof. exact (proj2 (@lem7025535 A t s h1)). Qed.
Lemma lem7028503 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term63 A t s) : term216 A t s.
Proof. exact (proj1 (@lem7025535 A t s h1)). Qed.
Lemma lem7028504 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) (h3 : @FINITE (A -> Prop) s) (h4 : term216 A t s) : (@FINITE (A -> Prop) s) = ((term142 A t s f) = (term632 A t s f)).
Proof. exact (prop_ext (fun h5 : @FINITE (A -> Prop) s => @lem7028501 A f t s h1 h2 h3 h4) (fun h5 : (term142 A t s f) = (term632 A t s f) => @lem7025536 A s h3)). Qed.
Lemma lem7028505 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) (h3 : @FINITE (A -> Prop) s) (h4 : term216 A t s) : (term142 A t s f) = (term632 A t s f).
Proof. exact (EQ_MP (@lem7028504 A f t s h1 h2 h3 h4) (@lem7025536 A s h3)). Qed.
Lemma lem7028506 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) (h3 : @FINITE (A -> Prop) s) (h4 : term216 A t s) : (term216 A t s) = ((term142 A t s f) = (term632 A t s f)).
Proof. exact (prop_ext (fun h5 : term216 A t s => @lem7028505 A f t s h1 h2 h3 h4) (fun h5 : (term142 A t s f) = (term632 A t s f) => @lem7025537 A t s h4)). Qed.
Lemma lem7028507 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) (h3 : @FINITE (A -> Prop) s) (h4 : term216 A t s) : (term142 A t s f) = (term632 A t s f).
Proof. exact (EQ_MP (@lem7028506 A f t s h1 h2 h3 h4) (@lem7025537 A t s h4)). Qed.
Lemma lem7028508 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) (h3 : term216 A t s) (h4 : term63 A t s) : (@FINITE (A -> Prop) s) = ((term142 A t s f) = (term632 A t s f)).
Proof. exact (prop_ext (fun h5 : @FINITE (A -> Prop) s => @lem7028507 A f t s h1 h2 h5 h3) (fun h5 : (term142 A t s f) = (term632 A t s f) => @lem7028502 A t s h4)). Qed.
Lemma lem7028509 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) (h3 : term216 A t s) (h4 : term63 A t s) : (term142 A t s f) = (term632 A t s f).
Proof. exact (EQ_MP (@lem7028508 A f t s h1 h2 h3 h4) (@lem7028502 A t s h4)). Qed.
Lemma lem7028510 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) (h3 : term63 A t s) : (term216 A t s) = ((term142 A t s f) = (term632 A t s f)).
Proof. exact (prop_ext (fun h4 : term216 A t s => @lem7028509 A f t s h1 h2 h4 h3) (fun h4 : (term142 A t s f) = (term632 A t s f) => @lem7028503 A t s h3)). Qed.
Lemma lem7028511 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) (h3 : term63 A t s) : (term142 A t s f) = (term632 A t s f).
Proof. exact (EQ_MP (@lem7028510 A f t s h1 h2 h3) (@lem7028503 A t s h3)). Qed.
Lemma lem7028512 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) : term444 A t s f.
Proof. exact (fun h0 : term63 A t s => @lem7028511 A f t s h1 h2 h0). Qed.
Lemma lem7028513 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) : (term132 A t s f) = (term444 A t s f).
Proof. exact (prop_ext (fun h3 : term132 A t s f => @lem7028512 A f t s h1 h2) (fun h3 : term444 A t s f => @lem7025534 A t s f h1)). Qed.
Lemma lem7028514 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) : term444 A t s f.
Proof. exact (EQ_MP (@lem7028513 A f t s h1 h2) (@lem7025534 A t s f h1)). Qed.
Lemma lem7028515 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) : (term107 A t s) = (term444 A t s f).
Proof. exact (prop_ext (fun h3 : term107 A t s => @lem7028514 A f t s h1 h2) (fun h3 : term444 A t s f => @lem7025520 A t s h2)). Qed.
Lemma lem7028516 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) : term444 A t s f.
Proof. exact (EQ_MP (@lem7028515 A f t s h1 h2) (@lem7025520 A t s h2)). Qed.
Lemma lem7028517 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term132 A t s f) (h2 : term107 A t s) (h3 : (term46 A s f) = (term47 A s f)) : term254 A t s f.
Proof. exact (EQ_MP (@lem7025506 A t s f h3) (@lem7028516 A f t s h1 h2)). Qed.
Lemma lem7028518 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) : term633 A t s f.
Proof. exact (fun h0 : (term46 A s f) = (term47 A s f) => @lem7028517 A t s f h1 h2 h0). Qed.
Lemma lem7028519 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) : term634 A t s f.
Proof. exact (conj (@lem7025491 A f t s h1 h2) (@lem7028518 A f t s h1 h2)). Qed.
Lemma lem7028520 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) : term257 A t s f.
Proof. exact (@lem7023733 A t s f (@lem7028519 A f t s h1 h2)). Qed.
Lemma lem7028521 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) : term154 A t s f.
Proof. exact (EQ_MP (@lem7023730 A f t s h2) (@lem7028520 A f t s h1 h2)). Qed.
Lemma lem7028522 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) : term153 A t s f.
Proof. exact (EQ_MP (@lem7019142 A t s f) (@lem7028521 A f t s h1 h2)). Qed.
Lemma lem7028523 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) (h3 : term65 A f t s) : (term142 A t s f) = (term145 A t s f).
Proof. exact (@lem7028522 A f t s h1 h2 (@lem7019135 A f t s h3)). Qed.
Lemma lem7028524 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term134 A t s f) : term132 A t s f.
Proof. exact (proj2 (@lem7019136 A t s f h1)). Qed.
Lemma lem7028525 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) (h1 : term134 A t s f) : term107 A t s.
Proof. exact (proj1 (@lem7019136 A t s f h1)). Qed.
Lemma lem7028526 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) (h3 : term65 A f t s) : (term132 A t s f) = ((term142 A t s f) = (term145 A t s f)).
Proof. exact (prop_ext (fun h4 : term132 A t s f => @lem7028523 A f t s h1 h2 h3) (fun h4 : (term142 A t s f) = (term145 A t s f) => @lem7019137 A t s f h1)). Qed.
Lemma lem7028527 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) (h3 : term65 A f t s) : (term142 A t s f) = (term145 A t s f).
Proof. exact (EQ_MP (@lem7028526 A f t s h1 h2 h3) (@lem7019137 A t s f h1)). Qed.
Lemma lem7028528 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) (h3 : term65 A f t s) : (term107 A t s) = ((term142 A t s f) = (term145 A t s f)).
Proof. exact (prop_ext (fun h4 : term107 A t s => @lem7028527 A f t s h1 h2 h3) (fun h4 : (term142 A t s f) = (term145 A t s f) => @lem7019138 A t s h2)). Qed.
Lemma lem7028529 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term132 A t s f) (h2 : term107 A t s) (h3 : term65 A f t s) : (term142 A t s f) = (term145 A t s f).
Proof. exact (EQ_MP (@lem7028528 A f t s h1 h2 h3) (@lem7019138 A t s h2)). Qed.
Lemma lem7028530 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) (h2 : term134 A t s f) (h3 : term65 A f t s) : (term132 A t s f) = ((term142 A t s f) = (term145 A t s f)).
Proof. exact (prop_ext (fun h4 : term132 A t s f => @lem7028529 A f t s h4 h1 h3) (fun h4 : (term142 A t s f) = (term145 A t s f) => @lem7028524 A t s f h2)). Qed.
Lemma lem7028531 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term107 A t s) (h2 : term134 A t s f) (h3 : term65 A f t s) : (term142 A t s f) = (term145 A t s f).
Proof. exact (EQ_MP (@lem7028530 A f t s h1 h2 h3) (@lem7028524 A t s f h2)). Qed.
Lemma lem7028532 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term134 A t s f) (h2 : term65 A f t s) : (term107 A t s) = ((term142 A t s f) = (term145 A t s f)).
Proof. exact (prop_ext (fun h3 : term107 A t s => @lem7028531 A f t s h3 h1 h2) (fun h3 : (term142 A t s f) = (term145 A t s f) => @lem7028525 A t s f h1)). Qed.
Lemma lem7028533 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term134 A t s f) (h2 : term65 A f t s) : (term142 A t s f) = (term145 A t s f).
Proof. exact (EQ_MP (@lem7028532 A f t s h1 h2) (@lem7028525 A t s f h1)). Qed.
Lemma lem7028534 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : type686 A) (h1 : term65 A f t s) : term146 A t s f.
Proof. exact (fun h0 : term134 A t s f => @lem7028533 A f t s h0 h1). Qed.
Lemma lem7028535 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> nat) : term147 A t s f.
Proof. exact (fun h0 : term65 A f t s => @lem7028534 A f t s h0). Qed.
Lemma lem7028540 {A : Type'} (t : A -> Prop) (f : A -> nat) : term149 A t f.
Proof. exact (fun s : type686 A => @lem7028535 A t s f). Qed.
Lemma lem7028545 {A : Type'} (f : A -> nat) : term151 A f.
Proof. exact (fun t : A -> Prop => @lem7028540 A t f). Qed.
Lemma lem7028546 {A : Type'} (f : A -> nat) : term81 A f.
Proof. exact (EQ_MP (@lem7019134 A f) (@lem7028545 A f)). Qed.
Lemma lem7028547 {A : Type'} (f : A -> nat) : term51 A f.
Proof. exact (@lem7018748 A f (@lem7028546 A f)). Qed.
Lemma lem7028548 {A : Type'} (f : A -> nat) : term50 A f.
Proof. exact (EQ_MP (@lem7018715 A f) (@lem7028547 A f)). Qed.
Lemma lem7028553 {A : Type'} : term635 A.
Proof. exact (fun f : A -> nat => @lem7028548 A f). Qed.
