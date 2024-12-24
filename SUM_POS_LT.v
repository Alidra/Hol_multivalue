Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_POS_LT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_LET_TRANS_spec.
Require Import SUM_0_spec.
Require Import SUM_LT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339240_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm7_spec.
Lemma lem7077575 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem7077576 {A : Type'} (f : A -> real) (h1 : term0 A) : term1 A f.
Proof. exact (@lem7077575 A h1 f). Qed.
Lemma lem7077577 {A : Type'} (f : A -> real) : (term1 A f) = (term2 A f).
Proof. exact (eq_refl (term1 A f)). Qed.
Lemma lem7077578 {A : Type'} (f : A -> real) (h1 : term0 A) : term2 A f.
Proof. exact (EQ_MP (@lem7077577 A f) (@lem7077576 A f h1)). Qed.
Lemma lem7077579 {A : Type'} (f : A -> real) (g : A -> real) (h1 : term0 A) : term3 A f g.
Proof. exact (@lem7077578 A f h1 g). Qed.
Lemma lem7077580 {A : Type'} (f : A -> real) (g : A -> real) : (term3 A f g) = (term4 A f g).
Proof. exact (eq_refl (term3 A f g)). Qed.
Lemma lem7077581 {A : Type'} (f : A -> real) (g : A -> real) (h1 : term0 A) : term4 A f g.
Proof. exact (EQ_MP (@lem7077580 A f g) (@lem7077579 A f g h1)). Qed.
Lemma lem7077582 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (h1 : term0 A) : term5 A f g s.
Proof. exact (@lem7077581 A f g h1 s). Qed.
Lemma lem7077583 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term5 A f g s) = (term6 A f s g).
Proof. exact (eq_refl (term5 A f g s)). Qed.
Lemma lem7077584 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term0 A) : term6 A f s g.
Proof. exact (EQ_MP (@lem7077583 A f s g) (@lem7077582 A f g s h1)). Qed.
Lemma lem7077585 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term7 A s f g) : term7 A s f g.
Proof. exact (h1). Qed.
Lemma lem7077586 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term0 A) (h2 : term7 A s f g) : term8 A f s g.
Proof. exact (@lem7077584 A f s g h1 (@lem7077585 A s f g h2)). Qed.
Lemma lem7077587 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term7 A s f g) : term9 A f s g.
Proof. exact (fun h0 : term0 A => @lem7077586 A s f g h0 h1). Qed.
Lemma lem7077588 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem7077589 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term0 A) (h2 : term7 A s f g) : term8 A f s g.
Proof. exact (@lem7077587 A s f g h2 (@lem7077588 A h1)). Qed.
Lemma lem7077590 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term0 A) : term6 A f s g.
Proof. exact (fun h0 : term7 A s f g => @lem7077589 A s f g h1 h0). Qed.
Lemma lem7077591 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term0 A) : term10 A f s.
Proof. exact (fun g : A -> real => @lem7077590 A f s g h1). Qed.
Lemma lem7077592 {A : Type'} (f : A -> real) (h1 : term0 A) : term11 A f.
Proof. exact (fun s : A -> Prop => @lem7077591 A f s h1). Qed.
Lemma lem7077593 {A : Type'} (h1 : term0 A) : term12 A.
Proof. exact (fun f : A -> real => @lem7077592 A f h1). Qed.
Lemma lem7077594 {A : Type'} : term13 A.
Proof. exact (fun h0 : term0 A => @lem7077593 A h0). Qed.
Lemma lem7077595 {A : Type'} : term12 A.
Proof. exact (@lem7077594 A (@lem7073063 A)). Qed.
Lemma lem7077596 {A : Type'} (f : A -> real) : term14 A f.
Proof. exact (@lem7077595 A f). Qed.
Lemma lem7077597 {A : Type'} (f : A -> real) : (term14 A f) = (term11 A f).
Proof. exact (eq_refl (term14 A f)). Qed.
Lemma lem7077598 {A : Type'} (f : A -> real) : term11 A f.
Proof. exact (EQ_MP (@lem7077597 A f) (@lem7077596 A f)). Qed.
Lemma lem7077599 {A : Type'} (f : A -> real) (s : A -> Prop) : term15 A f s.
Proof. exact (@lem7077598 A f s). Qed.
Lemma lem7077600 {A : Type'} (f : A -> real) (s : A -> Prop) : (term15 A f s) = (term10 A f s).
Proof. exact (eq_refl (term15 A f s)). Qed.
Lemma lem7077601 {A : Type'} (f : A -> real) (s : A -> Prop) : term10 A f s.
Proof. exact (EQ_MP (@lem7077600 A f s) (@lem7077599 A f s)). Qed.
Lemma lem7077602 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : term16 A f s g.
Proof. exact (@lem7077601 A f s g). Qed.
Lemma lem7077603 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term16 A f s g) = (term6 A f s g).
Proof. exact (eq_refl (term16 A f s g)). Qed.
Lemma lem7077605 (x : real) : term17 x.
Proof. exact (@lem1339240 x). Qed.
Lemma lem7077606 (x : real) : (term17 x) = (real_le x x).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem7077607 (x : real) : real_le x x.
Proof. exact (EQ_MP (@lem7077606 x) (@lem7077605 x)). Qed.
Lemma lem7077608 (x : real) : (real_le x x) = ((real_le x x) = True).
Proof. exact (@lem7 (real_le x x)). Qed.
Lemma lem7077610 {A : Type'} (s : A -> Prop) : term18 A s.
Proof. exact (@lem7069399 A s). Qed.
Lemma lem7077611 {A : Type'} (s : A -> Prop) : (term18 A s) = ((term19 A s) = term20).
Proof. exact (eq_refl (term18 A s)). Qed.
Lemma lem7077613 (h1 : term21) : term21.
Proof. exact (h1). Qed.
Lemma lem7077614 (x : real) (h1 : term21) : term22 x.
Proof. exact (@lem7077613 h1 x). Qed.
Lemma lem7077615 (x : real) : (term22 x) = (term23 x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem7077616 (x : real) (h1 : term21) : term23 x.
Proof. exact (EQ_MP (@lem7077615 x) (@lem7077614 x h1)). Qed.
Lemma lem7077617 (x : real) (y : real) (h1 : term21) : term24 x y.
Proof. exact (@lem7077616 x h1 y). Qed.
Lemma lem7077618 (y : real) (x : real) : (term24 x y) = (term25 y x).
Proof. exact (eq_refl (term24 x y)). Qed.
Lemma lem7077619 (y : real) (x : real) (h1 : term21) : term25 y x.
Proof. exact (EQ_MP (@lem7077618 y x) (@lem7077617 x y h1)). Qed.
Lemma lem7077620 (y : real) (x : real) (z : real) (h1 : term21) : term26 y x z.
Proof. exact (@lem7077619 y x h1 z). Qed.
Lemma lem7077621 (y : real) (x : real) (z : real) : (term26 y x z) = (term27 y x z).
Proof. exact (eq_refl (term26 y x z)). Qed.
Lemma lem7077622 (y : real) (x : real) (z : real) (h1 : term21) : term27 y x z.
Proof. exact (EQ_MP (@lem7077621 y x z) (@lem7077620 y x z h1)). Qed.
Lemma lem7077623 (x : real) (y : real) (z : real) (h1 : term28 x y z) : term28 x y z.
Proof. exact (h1). Qed.
Lemma lem7077624 (x : real) (y : real) (z : real) (h1 : term21) (h2 : term28 x y z) : real_lt x z.
Proof. exact (@lem7077622 y x z h1 (@lem7077623 x y z h2)). Qed.
Lemma lem7077625 (x : real) (y : real) (z : real) (h1 : term28 x y z) : term29 x z.
Proof. exact (fun h0 : term21 => @lem7077624 x y z h0 h1). Qed.
Lemma lem7077626 (x : real) (z : real) (h1 : term30 x z) : term30 x z.
Proof. exact (h1). Qed.
Lemma lem7077627 (x : real) (z : real) (h1 : term30 x z) : term29 x z.
Proof. exact (ex_elim (@lem7077626 x z h1) (fun y : real => fun h0 : term31 x z y => @lem7077625 x y z h0)). Qed.
Lemma lem7077628 (h1 : term21) : term21.
Proof. exact (h1). Qed.
Lemma lem7077629 (x : real) (z : real) (h1 : term21) (h2 : term30 x z) : real_lt x z.
Proof. exact (@lem7077627 x z h2 (@lem7077628 h1)). Qed.
Lemma lem7077630 (x : real) (z : real) (h1 : term21) : term32 x z.
Proof. exact (fun h0 : term30 x z => @lem7077629 x z h1 h0). Qed.
Lemma lem7077631 (x : real) (h1 : term21) : term33 x.
Proof. exact (fun z : real => @lem7077630 x z h1). Qed.
Lemma lem7077632 (h1 : term21) : term34.
Proof. exact (fun x : real => @lem7077631 x h1). Qed.
Lemma lem7077633 : term35.
Proof. exact (fun h0 : term21 => @lem7077632 h0). Qed.
Lemma lem7077634 : term34.
Proof. exact (@lem7077633 (@lem1371386)). Qed.
Lemma lem7077635 (x : real) : term36 x.
Proof. exact (@lem7077634 x). Qed.
Lemma lem7077636 (x : real) : (term36 x) = (term33 x).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem7077637 (x : real) : term33 x.
Proof. exact (EQ_MP (@lem7077636 x) (@lem7077635 x)). Qed.
Lemma lem7077638 (x : real) (z : real) : term37 x z.
Proof. exact (@lem7077637 x z). Qed.
Lemma lem7077639 (x : real) (z : real) : (term37 x z) = (term32 x z).
Proof. exact (eq_refl (term37 x z)). Qed.
Lemma lem7077641 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term38 A s f) : term38 A s f.
Proof. exact (h1). Qed.
Lemma lem7077642 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term39 A s f) : term39 A s f.
Proof. exact (h1). Qed.
Lemma lem7077643 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7077644 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term40 A s f) : term40 A s f.
Proof. exact (h1). Qed.
Lemma lem7077645 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term41 A s f) : term41 A s f.
Proof. exact (h1). Qed.
Lemma lem7077646 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term42 A s f x) : term42 A s f x.
Proof. exact (h1). Qed.
Lemma lem7077647 {A : Type'} (f : A -> real) (x : A) (h1 : term43 A f x) : term43 A f x.
Proof. exact (h1). Qed.
Lemma lem7077648 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem7077650 (x : real) (z : real) : term32 x z.
Proof. exact (EQ_MP (@lem7077639 x z) (@lem7077638 x z)). Qed.
Lemma lem7077651 {A : Type'} (s : A -> Prop) (f : A -> real) : term44 A s f.
Proof. exact (@lem7077650 term20 (@sum A s f)). Qed.
Lemma lem7077655 {A : Type'} (s : A -> Prop) : (term19 A s) = term20.
Proof. exact (EQ_MP (@lem7077611 A s) (@lem7077610 A s)). Qed.
Lemma lem7077656 {A : Type'} (s : A -> Prop) : (term19 A s) = term20.
Proof. exact (@lem7077655 A s). Qed.
Lemma lem7077657 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem7077658 {A : Type'} (s : A -> Prop) : (term46 A s) = term47.
Proof. exact (MK_COMB (@lem7077657) (@lem7077656 A s)). Qed.
Lemma lem7077660 (x : real) : (real_le x x) = True.
Proof. exact (EQ_MP (@lem7077608 x) (@lem7077607 x)). Qed.
Lemma lem7077661 : term47 = True.
Proof. exact (@lem7077660 term20). Qed.
Lemma lem7077662 {A : Type'} (s : A -> Prop) : (term46 A s) = True.
Proof. exact (TRANS (@lem7077658 A s) (@lem7077661)). Qed.
Lemma lem7077663 {A : Type'} (s : A -> Prop) : True = (term46 A s).
Proof. exact (SYM (@lem7077662 A s)). Qed.
Lemma lem7077664 {A : Type'} (s : A -> Prop) : term46 A s.
Proof. exact (EQ_MP (@lem7077663 A s) (@lem0)). Qed.
Lemma lem7077666 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : term6 A f s g.
Proof. exact (EQ_MP (@lem7077603 A f s g) (@lem7077602 A f s g)). Qed.
Lemma lem7077667 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : term6 A f s g.
Proof. exact (@lem7077666 A f s g). Qed.
Lemma lem7077668 {A : Type'} (s : A -> Prop) (f : A -> real) : term48 A s f.
Proof. exact (@lem7077667 A (term49 A) s f). Qed.
Lemma lem7077670 (p : Prop) : p = (term50 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7077671 {A : Type'} (s : A -> Prop) (f : A -> real) : (term51 A s f) = (term52 A s f).
Proof. exact (@lem7077670 (term51 A s f)). Qed.
Lemma lem7077672 {A : Type'} (s : A -> Prop) (f : A -> real) : (term52 A s f) = (term51 A s f).
Proof. exact (SYM (@lem7077671 A s f)). Qed.
Lemma lem7077673 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term53 A s f) : term53 A s f.
Proof. exact (h1). Qed.
Lemma lem7077676 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (h1 : term54 A x s f) : term54 A x s f.
Proof. exact (h1). Qed.
Lemma lem7077677 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : term55 A x s f.
Proof. exact (fun h0 : term54 A x s f => @lem7077676 A x s f h0). Qed.
Lemma lem7077678 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (h1 : term55 A x s f) : term55 A x s f.
Proof. exact (h1). Qed.
Lemma lem7077679 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (h1 : term54 A x s f) : term54 A x s f.
Proof. exact (h1). Qed.
Lemma lem7077680 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (h1 : term54 A x s f) (h2 : term55 A x s f) : term54 A x s f.
Proof. exact (@lem7077678 A x s f h2 (@lem7077679 A x s f h1)). Qed.
Lemma lem7077681 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (h1 : term54 A x s f) : term56 A x s f.
Proof. exact (fun h0 : term55 A x s f => @lem7077680 A x s f h1 h0). Qed.
Lemma lem7077682 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (h1 : term55 A x s f) : term55 A x s f.
Proof. exact (h1). Qed.
Lemma lem7077683 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (h1 : term54 A x s f) (h2 : term55 A x s f) : term54 A x s f.
Proof. exact (@lem7077681 A x s f h1 (@lem7077682 A x s f h2)). Qed.
Lemma lem7077684 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (h1 : term55 A x s f) : term55 A x s f.
Proof. exact (fun h0 : term54 A x s f => @lem7077683 A x s f h0 h1). Qed.
Lemma lem7077685 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : term57 A x s f.
Proof. exact (fun h0 : term55 A x s f => @lem7077684 A x s f h0). Qed.
Lemma lem7077688 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : term55 A x s f.
Proof. exact (@lem7077685 A x s f (@lem7077677 A x s f)). Qed.
Lemma lem7077689 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : term55 A x s f.
Proof. exact (@lem7077688 A x s f). Qed.
Lemma lem7077717 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7077718 {A : Type'} (s : A -> Prop) (f : A -> real) : (term52 A s f) = (term58 A s f).
Proof. exact (@lem7077717 (term53 A s f)). Qed.
Lemma lem7077720 (t : Prop) : (term59 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7077721 {A : Type'} (s : A -> Prop) (f : A -> real) : (term58 A s f) = (term51 A s f).
Proof. exact (@lem7077720 (term51 A s f)). Qed.
Lemma lem7077724 {A : Type'} (s : A -> Prop) (f : A -> real) : (term52 A s f) = (term51 A s f).
Proof. exact (TRANS (@lem7077718 A s f) (@lem7077721 A s f)). Qed.
Lemma lem7077783 {A : Type'} (f : A -> real) (x : A) : (term60 A f x) = (term60 A f x).
Proof. exact (eq_refl (term60 A f x)). Qed.
Lemma lem7077784 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term61 A x s f) = (term62 A x s f).
Proof. exact (MK_COMB (@lem7077783 A f x) (@lem7077724 A s f)). Qed.
Lemma lem7077787 {A : Type'} (x : A) (s : A -> Prop) : (term63 A x s) = (term63 A x s).
Proof. exact (eq_refl (term63 A x s)). Qed.
Lemma lem7077788 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term64 A x s f) = (term65 A x s f).
Proof. exact (MK_COMB (@lem7077787 A x s) (@lem7077784 A x s f)). Qed.
Lemma lem7077791 {A : Type'} (s : A -> Prop) (f : A -> real) : (term66 A s f) = (term66 A s f).
Proof. exact (eq_refl (term66 A s f)). Qed.
Lemma lem7077792 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term67 A x s f) = (term68 A x s f).
Proof. exact (MK_COMB (@lem7077791 A s f) (@lem7077788 A x s f)). Qed.
Lemma lem7077795 {A : Type'} (s : A -> Prop) : (term69 A s) = (term69 A s).
Proof. exact (eq_refl (term69 A s)). Qed.
Lemma lem7077796 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term54 A x s f) = (term70 A x s f).
Proof. exact (MK_COMB (@lem7077795 A s) (@lem7077792 A x s f)). Qed.
Lemma lem7077799 {A : Type'} (s : A -> Prop) (f : A -> real) : (term71 A s f) = (term72 A s f).
Proof. exact (fun_ext (fun x : A => @lem7077796 A x s f)). Qed.
Lemma lem7077800 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7077801 {A : Type'} (s : A -> Prop) (f : A -> real) : (term73 A s f) = (term74 A s f).
Proof. exact (MK_COMB (@lem7077800 A) (@lem7077799 A s f)). Qed.
Lemma lem7077806 {A : Type'} (f : A -> real) : (term75 A f) = (term76 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7077801 A s f)). Qed.
Lemma lem7077807 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7077808 {A : Type'} (f : A -> real) : (term77 A f) = (term78 A f).
Proof. exact (MK_COMB (@lem7077807 A) (@lem7077806 A f)). Qed.
Lemma lem7077813 {A : Type'} : (term79 A) = (term80 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7077808 A f)). Qed.
Lemma lem7077814 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7077815 {A : Type'} : (term81 A) = (term82 A).
Proof. exact (MK_COMB (@lem7077814 A) (@lem7077813 A)). Qed.
Lemma lem7077820 {A : Type'} (x : A) : (term83 A x) = term20.
Proof. exact (eq_refl (term83 A x)). Qed.
Lemma lem7077821 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7077822 {A : Type'} (x : A) : (term84 A x) = term45.
Proof. exact (MK_COMB (@lem7077821) (@lem7077820 A x)). Qed.
Lemma lem7077823 {A : Type'} (f : A -> real) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem7077824 {A : Type'} (f : A -> real) (x : A) : (term85 A f x) = (term86 A f x).
Proof. exact (MK_COMB (@lem7077822 A x) (@lem7077823 A f x)). Qed.
Lemma lem7077825 {A : Type'} (x : A) (s : A -> Prop) : (term63 A x s) = (term63 A x s).
Proof. exact (eq_refl (term63 A x s)). Qed.
Lemma lem7077826 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term87 A s f x) = (term88 A s f x).
Proof. exact (MK_COMB (@lem7077825 A x s) (@lem7077824 A f x)). Qed.
Lemma lem7077827 {A : Type'} (s : A -> Prop) (f : A -> real) : (term89 A s f) = (term90 A s f).
Proof. exact (fun_ext (fun x : A => @lem7077826 A s f x)). Qed.
Lemma lem7077828 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7077829 {A : Type'} (s : A -> Prop) (f : A -> real) : (term91 A s f) = (term41 A s f).
Proof. exact (MK_COMB (@lem7077828 A) (@lem7077827 A s f)). Qed.
Lemma lem7077830 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7077831 {A : Type'} (s : A -> Prop) (f : A -> real) : (term92 A s f) = (term93 A s f).
Proof. exact (MK_COMB (@lem7077830) (@lem7077829 A s f)). Qed.
Lemma lem7077832 {A : Type'} (x : A) : (term83 A x) = term20.
Proof. exact (eq_refl (term83 A x)). Qed.
Lemma lem7077833 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7077834 {A : Type'} (x : A) : (term94 A x) = term95.
Proof. exact (MK_COMB (@lem7077833) (@lem7077832 A x)). Qed.
Lemma lem7077835 {A : Type'} (f : A -> real) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem7077836 {A : Type'} (f : A -> real) (x : A) : (term96 A f x) = (term43 A f x).
Proof. exact (MK_COMB (@lem7077834 A x) (@lem7077835 A f x)). Qed.
Lemma lem7077837 {A : Type'} (x : A) (s : A -> Prop) : (term97 A x s) = (term97 A x s).
Proof. exact (eq_refl (term97 A x s)). Qed.
Lemma lem7077838 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term98 A s f x) = (term42 A s f x).
Proof. exact (MK_COMB (@lem7077837 A x s) (@lem7077836 A f x)). Qed.
Lemma lem7077839 {A : Type'} (s : A -> Prop) (f : A -> real) : (term99 A s f) = (term100 A s f).
Proof. exact (fun_ext (fun x : A => @lem7077838 A s f x)). Qed.
Lemma lem7077840 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7077841 {A : Type'} (s : A -> Prop) (f : A -> real) : (term101 A s f) = (term40 A s f).
Proof. exact (MK_COMB (@lem7077840 A) (@lem7077839 A s f)). Qed.
Lemma lem7077842 {A : Type'} (s : A -> Prop) (f : A -> real) : (term102 A s f) = (term39 A s f).
Proof. exact (MK_COMB (@lem7077831 A s f) (@lem7077841 A s f)). Qed.
Lemma lem7077843 {A : Type'} (s : A -> Prop) : (term103 A s) = (term103 A s).
Proof. exact (eq_refl (term103 A s)). Qed.
Lemma lem7077844 {A : Type'} (s : A -> Prop) (f : A -> real) : (term51 A s f) = (term38 A s f).
Proof. exact (MK_COMB (@lem7077843 A s) (@lem7077842 A s f)). Qed.
Lemma lem7077845 {A : Type'} (f : A -> real) (x : A) : (term60 A f x) = (term60 A f x).
Proof. exact (eq_refl (term60 A f x)). Qed.
Lemma lem7077846 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term62 A x s f) = (term104 A x s f).
Proof. exact (MK_COMB (@lem7077845 A f x) (@lem7077844 A s f)). Qed.
Lemma lem7077847 {A : Type'} (x : A) (s : A -> Prop) : (term63 A x s) = (term63 A x s).
Proof. exact (eq_refl (term63 A x s)). Qed.
Lemma lem7077848 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term65 A x s f) = (term105 A x s f).
Proof. exact (MK_COMB (@lem7077847 A x s) (@lem7077846 A x s f)). Qed.
Lemma lem7077849 {A : Type'} (s : A -> Prop) (f : A -> real) : (term66 A s f) = (term66 A s f).
Proof. exact (eq_refl (term66 A s f)). Qed.
Lemma lem7077850 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term68 A x s f) = (term106 A x s f).
Proof. exact (MK_COMB (@lem7077849 A s f) (@lem7077848 A x s f)). Qed.
Lemma lem7077851 {A : Type'} (s : A -> Prop) : (term69 A s) = (term69 A s).
Proof. exact (eq_refl (term69 A s)). Qed.
Lemma lem7077852 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term70 A x s f) = (term107 A x s f).
Proof. exact (MK_COMB (@lem7077851 A s) (@lem7077850 A x s f)). Qed.
Lemma lem7077853 {A : Type'} (s : A -> Prop) (f : A -> real) : (term72 A s f) = (term108 A s f).
Proof. exact (fun_ext (fun x : A => @lem7077852 A x s f)). Qed.
Lemma lem7077854 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7077855 {A : Type'} (s : A -> Prop) (f : A -> real) : (term74 A s f) = (term109 A s f).
Proof. exact (MK_COMB (@lem7077854 A) (@lem7077853 A s f)). Qed.
Lemma lem7077856 {A : Type'} (f : A -> real) : (term76 A f) = (term110 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7077855 A s f)). Qed.
Lemma lem7077857 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7077858 {A : Type'} (f : A -> real) : (term78 A f) = (term111 A f).
Proof. exact (MK_COMB (@lem7077857 A) (@lem7077856 A f)). Qed.
Lemma lem7077859 {A : Type'} : (term80 A) = (term112 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7077858 A f)). Qed.
Lemma lem7077860 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7077861 {A : Type'} : (term82 A) = (term113 A).
Proof. exact (MK_COMB (@lem7077860 A) (@lem7077859 A)). Qed.
Lemma lem7077864 {A : Type'} : (term81 A) = (term113 A).
Proof. exact (TRANS (@lem7077815 A) (@lem7077861 A)). Qed.
Lemma lem7077869 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term42 A s f x) = (term42 A s f x).
Proof. exact (eq_refl (term42 A s f x)). Qed.
Lemma lem7077870 {A : Type'} (s : A -> Prop) (f : A -> real) : (term100 A s f) = (term100 A s f).
Proof. exact (fun_ext (fun x : A => @lem7077869 A s f x)). Qed.
Lemma lem7077871 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7077872 {A : Type'} (s : A -> Prop) (f : A -> real) : (term40 A s f) = (term40 A s f).
Proof. exact (MK_COMB (@lem7077871 A) (@lem7077870 A s f)). Qed.
Lemma lem7077877 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term88 A s f x) = (term88 A s f x).
Proof. exact (eq_refl (term88 A s f x)). Qed.
Lemma lem7077878 {A : Type'} (s : A -> Prop) (f : A -> real) : (term90 A s f) = (term90 A s f).
Proof. exact (fun_ext (fun x : A => @lem7077877 A s f x)). Qed.
Lemma lem7077879 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7077880 {A : Type'} (s : A -> Prop) (f : A -> real) : (term41 A s f) = (term41 A s f).
Proof. exact (MK_COMB (@lem7077879 A) (@lem7077878 A s f)). Qed.
Lemma lem7077881 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7077882 {A : Type'} (s : A -> Prop) (f : A -> real) : (term93 A s f) = (term93 A s f).
Proof. exact (MK_COMB (@lem7077881) (@lem7077880 A s f)). Qed.
Lemma lem7077883 {A : Type'} (s : A -> Prop) (f : A -> real) : (term39 A s f) = (term39 A s f).
Proof. exact (MK_COMB (@lem7077882 A s f) (@lem7077872 A s f)). Qed.
Lemma lem7077886 {A : Type'} (s : A -> Prop) : (term103 A s) = (term103 A s).
Proof. exact (eq_refl (term103 A s)). Qed.
Lemma lem7077887 {A : Type'} (s : A -> Prop) (f : A -> real) : (term38 A s f) = (term38 A s f).
Proof. exact (MK_COMB (@lem7077886 A s) (@lem7077883 A s f)). Qed.
Lemma lem7077890 {A : Type'} (f : A -> real) (x : A) : (term60 A f x) = (term60 A f x).
Proof. exact (eq_refl (term60 A f x)). Qed.
Lemma lem7077891 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term104 A x s f) = (term104 A x s f).
Proof. exact (MK_COMB (@lem7077890 A f x) (@lem7077887 A s f)). Qed.
Lemma lem7077894 {A : Type'} (x : A) (s : A -> Prop) : (term63 A x s) = (term63 A x s).
Proof. exact (eq_refl (term63 A x s)). Qed.
Lemma lem7077895 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term105 A x s f) = (term105 A x s f).
Proof. exact (MK_COMB (@lem7077894 A x s) (@lem7077891 A x s f)). Qed.
Lemma lem7077900 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term88 A s f x) = (term88 A s f x).
Proof. exact (eq_refl (term88 A s f x)). Qed.
Lemma lem7077901 {A : Type'} (s : A -> Prop) (f : A -> real) : (term90 A s f) = (term90 A s f).
Proof. exact (fun_ext (fun x : A => @lem7077900 A s f x)). Qed.
Lemma lem7077902 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7077903 {A : Type'} (s : A -> Prop) (f : A -> real) : (term41 A s f) = (term41 A s f).
Proof. exact (MK_COMB (@lem7077902 A) (@lem7077901 A s f)). Qed.
Lemma lem7077904 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7077905 {A : Type'} (s : A -> Prop) (f : A -> real) : (term66 A s f) = (term66 A s f).
Proof. exact (MK_COMB (@lem7077904) (@lem7077903 A s f)). Qed.
Lemma lem7077906 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term106 A x s f) = (term106 A x s f).
Proof. exact (MK_COMB (@lem7077905 A s f) (@lem7077895 A x s f)). Qed.
Lemma lem7077909 {A : Type'} (s : A -> Prop) : (term69 A s) = (term69 A s).
Proof. exact (eq_refl (term69 A s)). Qed.
Lemma lem7077910 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term107 A x s f) = (term107 A x s f).
Proof. exact (MK_COMB (@lem7077909 A s) (@lem7077906 A x s f)). Qed.
Lemma lem7077911 {A : Type'} (s : A -> Prop) (f : A -> real) : (term108 A s f) = (term108 A s f).
Proof. exact (fun_ext (fun x : A => @lem7077910 A x s f)). Qed.
Lemma lem7077912 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7077913 {A : Type'} (s : A -> Prop) (f : A -> real) : (term109 A s f) = (term109 A s f).
Proof. exact (MK_COMB (@lem7077912 A) (@lem7077911 A s f)). Qed.
Lemma lem7077914 {A : Type'} (f : A -> real) : (term110 A f) = (term110 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7077913 A s f)). Qed.
Lemma lem7077915 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7077916 {A : Type'} (f : A -> real) : (term111 A f) = (term111 A f).
Proof. exact (MK_COMB (@lem7077915 A) (@lem7077914 A f)). Qed.
Lemma lem7077917 {A : Type'} : (term112 A) = (term112 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7077916 A f)). Qed.
Lemma lem7077918 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7077919 {A : Type'} : (term113 A) = (term113 A).
Proof. exact (MK_COMB (@lem7077918 A) (@lem7077917 A)). Qed.
Lemma lem7077976 {A : Type'} : (term81 A) = (term113 A).
Proof. exact (TRANS (@lem7077864 A) (@lem7077919 A)). Qed.
Lemma lem7077977 {A : Type'} : (term113 A) = (term81 A).
Proof. exact (SYM (@lem7077976 A)). Qed.
Lemma lem7077979 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term41 A s f) : term41 A s f.
Proof. exact (h1). Qed.
Lemma lem7077983 (p : Prop) : p = (term50 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7077984 {A : Type'} (s : A -> Prop) (f : A -> real) : (term38 A s f) = (term114 A s f).
Proof. exact (@lem7077983 (term38 A s f)). Qed.
Lemma lem7077985 {A : Type'} (s : A -> Prop) (f : A -> real) : (term114 A s f) = (term38 A s f).
Proof. exact (SYM (@lem7077984 A s f)). Qed.
Lemma lem7077986 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term115 A s f) : term115 A s f.
Proof. exact (h1). Qed.
Lemma lem7077992 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7077999 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term88 A s f x) = (term116 A s f x).
Proof. exact (@lem17265 (@IN A x s) (term86 A f x)). Qed.
Lemma lem7078000 {A : Type'} (s : A -> Prop) (f : A -> real) : (term90 A s f) = (term117 A s f).
Proof. exact (fun_ext (fun x : A => @lem7077999 A s f x)). Qed.
Lemma lem7078001 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7078054 {A : Type'} (s : A -> Prop) (f : A -> real) : (term41 A s f) = (term118 A s f).
Proof. exact (MK_COMB (@lem7078001 A) (@lem7078000 A s f)). Qed.
Lemma lem7078055 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term41 A s f) : term118 A s f.
Proof. exact (EQ_MP (@lem7078054 A s f) (@lem7077979 A s f h1)). Qed.
Lemma lem7078061 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem7078067 {A : Type'} (f : A -> real) (x : A) (h1 : term43 A f x) : term43 A f x.
Proof. exact (h1). Qed.
Lemma lem7078075 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term119 A s f x) = (term120 A s f x).
Proof. exact (@lem17362 (@IN A x s) (term86 A f x)). Qed.
Lemma lem7078076 {A : Type'} (P : A -> Prop) : (term121 A P) = (term122 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7078077 {A : Type'} (s : A -> Prop) (f : A -> real) : (term123 A s f) = (term124 A s f).
Proof. exact (@lem7078076 A (term90 A s f)). Qed.
Lemma lem7078078 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term125 A s f x) = (term88 A s f x).
Proof. exact (eq_refl (term125 A s f x)). Qed.
Lemma lem7078079 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7078080 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term126 A s f x) = (term119 A s f x).
Proof. exact (MK_COMB (@lem7078079) (@lem7078078 A s f x)). Qed.
Lemma lem7078081 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term126 A s f x) = (term120 A s f x).
Proof. exact (TRANS (@lem7078080 A s f x) (@lem7078075 A s f x)). Qed.
Lemma lem7078082 {A : Type'} (s : A -> Prop) (f : A -> real) : (term127 A s f) = (term128 A s f).
Proof. exact (fun_ext (fun x : A => @lem7078081 A s f x)). Qed.
Lemma lem7078083 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7078084 {A : Type'} (s : A -> Prop) (f : A -> real) : (term124 A s f) = (term129 A s f).
Proof. exact (MK_COMB (@lem7078083 A) (@lem7078082 A s f)). Qed.
Lemma lem7078085 {A : Type'} (s : A -> Prop) (f : A -> real) : (term123 A s f) = (term129 A s f).
Proof. exact (TRANS (@lem7078077 A s f) (@lem7078084 A s f)). Qed.
Lemma lem7078092 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term130 A s f x) = (term131 A s f x).
Proof. exact (@lem17045 (@IN A x s) (term43 A f x)). Qed.
Lemma lem7078093 {A : Type'} (P : A -> Prop) : (term132 A P) = (term133 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem7078094 {A : Type'} (s : A -> Prop) (f : A -> real) : (term134 A s f) = (term135 A s f).
Proof. exact (@lem7078093 A (term100 A s f)). Qed.
Lemma lem7078095 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term136 A s f x) = (term42 A s f x).
Proof. exact (eq_refl (term136 A s f x)). Qed.
Lemma lem7078096 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7078097 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term137 A s f x) = (term130 A s f x).
Proof. exact (MK_COMB (@lem7078096) (@lem7078095 A s f x)). Qed.
Lemma lem7078098 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term137 A s f x) = (term131 A s f x).
Proof. exact (TRANS (@lem7078097 A s f x) (@lem7078092 A s f x)). Qed.
Lemma lem7078099 {A : Type'} (s : A -> Prop) (f : A -> real) : (term138 A s f) = (term139 A s f).
Proof. exact (fun_ext (fun x : A => @lem7078098 A s f x)). Qed.
Lemma lem7078100 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7078101 {A : Type'} (s : A -> Prop) (f : A -> real) : (term135 A s f) = (term140 A s f).
Proof. exact (MK_COMB (@lem7078100 A) (@lem7078099 A s f)). Qed.
Lemma lem7078102 {A : Type'} (s : A -> Prop) (f : A -> real) : (term134 A s f) = (term140 A s f).
Proof. exact (TRANS (@lem7078094 A s f) (@lem7078101 A s f)). Qed.
Lemma lem7078103 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7078104 {A : Type'} (s : A -> Prop) (f : A -> real) : (term141 A s f) = (term142 A s f).
Proof. exact (MK_COMB (@lem7078103) (@lem7078085 A s f)). Qed.
Lemma lem7078105 {A : Type'} (s : A -> Prop) (f : A -> real) : (term143 A s f) = (term144 A s f).
Proof. exact (MK_COMB (@lem7078104 A s f) (@lem7078102 A s f)). Qed.
Lemma lem7078106 {A : Type'} (s : A -> Prop) (f : A -> real) : (term145 A s f) = (term143 A s f).
Proof. exact (@lem17045 (term41 A s f) (term40 A s f)). Qed.
Lemma lem7078107 {A : Type'} (s : A -> Prop) (f : A -> real) : (term145 A s f) = (term144 A s f).
Proof. exact (TRANS (@lem7078106 A s f) (@lem7078105 A s f)). Qed.
Lemma lem7078109 {A : Type'} (s : A -> Prop) : (term146 A s) = (term146 A s).
Proof. exact (eq_refl (term146 A s)). Qed.
Lemma lem7078110 {A : Type'} (s : A -> Prop) (f : A -> real) : (term147 A s f) = (term148 A s f).
Proof. exact (MK_COMB (@lem7078109 A s) (@lem7078107 A s f)). Qed.
Lemma lem7078111 {A : Type'} (s : A -> Prop) (f : A -> real) : (term115 A s f) = (term147 A s f).
Proof. exact (@lem17045 (@FINITE A s) (term39 A s f)). Qed.
Lemma lem7078112 {A : Type'} (s : A -> Prop) (f : A -> real) : (term115 A s f) = (term148 A s f).
Proof. exact (TRANS (@lem7078111 A s f) (@lem7078110 A s f)). Qed.
Lemma lem7078211 {A : Type'} (P : A -> Prop) (Q : Prop) : (term149 A P Q) = (term150 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7078212 {A : Type'} (P : A -> Prop) (Q : Prop) : (term149 A P Q) = (term150 A P Q).
Proof. exact (@lem7078211 A P Q). Qed.
Lemma lem7078213 {A : Type'} (s : A -> Prop) (f : A -> real) : (term151 A s f) = (term152 A s f).
Proof. exact (@lem7078212 A (term128 A s f) (term140 A s f)). Qed.
Lemma lem7078214 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term153 A s f x) = (term120 A s f x).
Proof. exact (eq_refl (term153 A s f x)). Qed.
Lemma lem7078215 {A : Type'} (s : A -> Prop) (f : A -> real) : (term154 A s f) = (term128 A s f).
Proof. exact (fun_ext (fun x : A => @lem7078214 A s f x)). Qed.
Lemma lem7078216 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7078217 {A : Type'} (s : A -> Prop) (f : A -> real) : (term155 A s f) = (term129 A s f).
Proof. exact (MK_COMB (@lem7078216 A) (@lem7078215 A s f)). Qed.
Lemma lem7078218 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7078219 {A : Type'} (s : A -> Prop) (f : A -> real) : (term156 A s f) = (term142 A s f).
Proof. exact (MK_COMB (@lem7078218) (@lem7078217 A s f)). Qed.
Lemma lem7078220 {A : Type'} (s : A -> Prop) (f : A -> real) : (term140 A s f) = (term140 A s f).
Proof. exact (eq_refl (term140 A s f)). Qed.
Lemma lem7078221 {A : Type'} (s : A -> Prop) (f : A -> real) : (term151 A s f) = (term144 A s f).
Proof. exact (MK_COMB (@lem7078219 A s f) (@lem7078220 A s f)). Qed.
Lemma lem7078222 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7078223 {A : Type'} (s : A -> Prop) (f : A -> real) : (term157 A s f) = (term158 A s f).
Proof. exact (MK_COMB (@lem7078222) (@lem7078221 A s f)). Qed.
Lemma lem7078224 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term153 A s f x) = (term120 A s f x).
Proof. exact (eq_refl (term153 A s f x)). Qed.
Lemma lem7078225 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7078226 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term159 A s f x) = (term160 A s f x).
Proof. exact (MK_COMB (@lem7078225) (@lem7078224 A s f x)). Qed.
Lemma lem7078227 {A : Type'} (s : A -> Prop) (f : A -> real) : (term140 A s f) = (term140 A s f).
Proof. exact (eq_refl (term140 A s f)). Qed.
Lemma lem7078228 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term161 A x s f) = (term162 A x s f).
Proof. exact (MK_COMB (@lem7078226 A s f x) (@lem7078227 A s f)). Qed.
Lemma lem7078229 {A : Type'} (s : A -> Prop) (f : A -> real) : (term163 A s f) = (term164 A s f).
Proof. exact (fun_ext (fun x : A => @lem7078228 A x s f)). Qed.
Lemma lem7078230 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7078231 {A : Type'} (s : A -> Prop) (f : A -> real) : (term152 A s f) = (term165 A s f).
Proof. exact (MK_COMB (@lem7078230 A) (@lem7078229 A s f)). Qed.
Lemma lem7078232 {A : Type'} (s : A -> Prop) (f : A -> real) : ((term151 A s f) = (term152 A s f)) = ((term144 A s f) = (term165 A s f)).
Proof. exact (MK_COMB (@lem7078223 A s f) (@lem7078231 A s f)). Qed.
Lemma lem7078233 {A : Type'} (s : A -> Prop) (f : A -> real) : (term144 A s f) = (term165 A s f).
Proof. exact (EQ_MP (@lem7078232 A s f) (@lem7078213 A s f)). Qed.
Lemma lem7078234 {A : Type'} (s : A -> Prop) : (term146 A s) = (term146 A s).
Proof. exact (eq_refl (term146 A s)). Qed.
Lemma lem7078235 {A : Type'} (s : A -> Prop) (f : A -> real) : (term148 A s f) = (term166 A s f).
Proof. exact (MK_COMB (@lem7078234 A s) (@lem7078233 A s f)). Qed.
Lemma lem7078237 {A : Type'} (P : Prop) (Q : A -> Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7078238 {A : Type'} (P : Prop) (Q : A -> Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (@lem7078237 A P Q). Qed.
Lemma lem7078239 {A : Type'} (s : A -> Prop) (f : A -> real) : (term169 A s f) = (term170 A s f).
Proof. exact (@lem7078238 A (term171 A s) (term164 A s f)). Qed.
Lemma lem7078240 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term172 A s f x) = (term162 A x s f).
Proof. exact (eq_refl (term172 A s f x)). Qed.
Lemma lem7078241 {A : Type'} (s : A -> Prop) (f : A -> real) : (term173 A s f) = (term164 A s f).
Proof. exact (fun_ext (fun x : A => @lem7078240 A x s f)). Qed.
Lemma lem7078242 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7078243 {A : Type'} (s : A -> Prop) (f : A -> real) : (term174 A s f) = (term165 A s f).
Proof. exact (MK_COMB (@lem7078242 A) (@lem7078241 A s f)). Qed.
Lemma lem7078244 {A : Type'} (s : A -> Prop) : (term146 A s) = (term146 A s).
Proof. exact (eq_refl (term146 A s)). Qed.
Lemma lem7078245 {A : Type'} (s : A -> Prop) (f : A -> real) : (term169 A s f) = (term166 A s f).
Proof. exact (MK_COMB (@lem7078244 A s) (@lem7078243 A s f)). Qed.
Lemma lem7078246 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7078247 {A : Type'} (s : A -> Prop) (f : A -> real) : (term175 A s f) = (term176 A s f).
Proof. exact (MK_COMB (@lem7078246) (@lem7078245 A s f)). Qed.
Lemma lem7078248 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term172 A s f x) = (term162 A x s f).
Proof. exact (eq_refl (term172 A s f x)). Qed.
Lemma lem7078249 {A : Type'} (s : A -> Prop) : (term146 A s) = (term146 A s).
Proof. exact (eq_refl (term146 A s)). Qed.
Lemma lem7078250 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term177 A s f x) = (term178 A x s f).
Proof. exact (MK_COMB (@lem7078249 A s) (@lem7078248 A x s f)). Qed.
Lemma lem7078251 {A : Type'} (s : A -> Prop) (f : A -> real) : (term179 A s f) = (term180 A s f).
Proof. exact (fun_ext (fun x : A => @lem7078250 A x s f)). Qed.
Lemma lem7078252 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7078253 {A : Type'} (s : A -> Prop) (f : A -> real) : (term170 A s f) = (term181 A s f).
Proof. exact (MK_COMB (@lem7078252 A) (@lem7078251 A s f)). Qed.
Lemma lem7078254 {A : Type'} (s : A -> Prop) (f : A -> real) : ((term169 A s f) = (term170 A s f)) = ((term166 A s f) = (term181 A s f)).
Proof. exact (MK_COMB (@lem7078247 A s f) (@lem7078253 A s f)). Qed.
Lemma lem7078255 {A : Type'} (s : A -> Prop) (f : A -> real) : (term166 A s f) = (term181 A s f).
Proof. exact (EQ_MP (@lem7078254 A s f) (@lem7078239 A s f)). Qed.
Lemma lem7078257 {A : Type'} (s : A -> Prop) (f : A -> real) : (term148 A s f) = (term181 A s f).
Proof. exact (TRANS (@lem7078235 A s f) (@lem7078255 A s f)). Qed.
Lemma lem7078258 {A : Type'} (s : A -> Prop) (f : A -> real) : (term115 A s f) = (term181 A s f).
Proof. exact (TRANS (@lem7078112 A s f) (@lem7078257 A s f)). Qed.
Lemma lem7078259 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term115 A s f) : term181 A s f.
Proof. exact (EQ_MP (@lem7078258 A s f) (@lem7077986 A s f h1)). Qed.
Lemma lem7078260 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (h1 : term178 A x' s f) : term178 A x' s f.
Proof. exact (h1). Qed.
Lemma lem7078264 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7078285 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term116 A s f x) = (term116 A s f x).
Proof. exact (eq_refl (term116 A s f x)). Qed.
Lemma lem7078286 {A : Type'} (s : A -> Prop) (f : A -> real) : (term117 A s f) = (term117 A s f).
Proof. exact (fun_ext (fun x : A => @lem7078285 A s f x)). Qed.
Lemma lem7078287 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7078288 {A : Type'} (s : A -> Prop) (f : A -> real) : (term118 A s f) = (term118 A s f).
Proof. exact (MK_COMB (@lem7078287 A) (@lem7078286 A s f)). Qed.
Lemma lem7078289 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term41 A s f) : term118 A s f.
Proof. exact (EQ_MP (@lem7078288 A s f) (@lem7078055 A s f h1)). Qed.
Lemma lem7078295 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem7078307 {A : Type'} (f : A -> real) (x : A) (h1 : term43 A f x) : term43 A f x.
Proof. exact (h1). Qed.
Lemma lem7078330 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term131 A s f x) = (term131 A s f x).
Proof. exact (eq_refl (term131 A s f x)). Qed.
Lemma lem7078331 {A : Type'} (s : A -> Prop) (f : A -> real) : (term139 A s f) = (term139 A s f).
Proof. exact (fun_ext (fun x : A => @lem7078330 A s f x)). Qed.
Lemma lem7078332 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7078333 {A : Type'} (s : A -> Prop) (f : A -> real) : (term140 A s f) = (term140 A s f).
Proof. exact (MK_COMB (@lem7078332 A) (@lem7078331 A s f)). Qed.
Lemma lem7078356 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) : (term160 A s f x') = (term160 A s f x').
Proof. exact (eq_refl (term160 A s f x')). Qed.
Lemma lem7078357 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) : (term162 A x' s f) = (term162 A x' s f).
Proof. exact (MK_COMB (@lem7078356 A s f x') (@lem7078333 A s f)). Qed.
Lemma lem7078364 {A : Type'} (s : A -> Prop) : (term146 A s) = (term146 A s).
Proof. exact (eq_refl (term146 A s)). Qed.
Lemma lem7078365 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) : (term178 A x' s f) = (term178 A x' s f).
Proof. exact (MK_COMB (@lem7078364 A s) (@lem7078357 A x' s f)). Qed.
Lemma lem7078366 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (h1 : term178 A x' s f) : term178 A x' s f.
Proof. exact (EQ_MP (@lem7078365 A x' s f) (@lem7078260 A x' s f h1)). Qed.
Lemma lem7078368 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (h1 : term162 A x' s f) : term162 A x' s f.
Proof. exact (h1). Qed.
Lemma lem7078369 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) (h1 : term120 A s f x') : term120 A s f x'.
Proof. exact (h1). Qed.
Lemma lem7078370 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term140 A s f) : term140 A s f.
Proof. exact (h1). Qed.
Lemma lem7078376 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7078401 {A : Type'} (s : A -> Prop) (h1 : term171 A s) : term171 A s.
Proof. exact (h1). Qed.
Lemma lem7078413 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term116 A s f x) = (term116 A s f x).
Proof. exact (eq_refl (term116 A s f x)). Qed.
Lemma lem7078414 {A : Type'} (s : A -> Prop) (f : A -> real) : (term117 A s f) = (term117 A s f).
Proof. exact (fun_ext (fun x : A => @lem7078413 A s f x)). Qed.
Lemma lem7078415 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7078417 {A : Type'} (s : A -> Prop) (f : A -> real) : (term118 A s f) = (term118 A s f).
Proof. exact (MK_COMB (@lem7078415 A) (@lem7078414 A s f)). Qed.
Lemma lem7078418 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term41 A s f) : term118 A s f.
Proof. exact (EQ_MP (@lem7078417 A s f) (@lem7078289 A s f h1)). Qed.
Lemma lem7078455 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem7078459 {A : Type'} (f : A -> real) (x : A) (h1 : term43 A f x) : term43 A f x.
Proof. exact (h1). Qed.
Lemma lem7078467 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term131 A s f x) = (term131 A s f x).
Proof. exact (eq_refl (term131 A s f x)). Qed.
Lemma lem7078468 {A : Type'} (s : A -> Prop) (f : A -> real) : (term139 A s f) = (term139 A s f).
Proof. exact (fun_ext (fun x : A => @lem7078467 A s f x)). Qed.
Lemma lem7078469 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7078471 {A : Type'} (s : A -> Prop) (f : A -> real) : (term140 A s f) = (term140 A s f).
Proof. exact (MK_COMB (@lem7078469 A) (@lem7078468 A s f)). Qed.
Lemma lem7078472 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term140 A s f) : term140 A s f.
Proof. exact (EQ_MP (@lem7078471 A s f) (@lem7078370 A s f h1)). Qed.
Lemma lem7078476 {A : Type'} (_94456 : A) (s : A -> Prop) (f : A -> real) (h1 : term41 A s f) : term182 A s f _94456.
Proof. exact (@lem7078418 A s f h1 _94456). Qed.
Lemma lem7078477 {A : Type'} (s : A -> Prop) (f : A -> real) (_94456 : A) : (term182 A s f _94456) = (term116 A s f _94456).
Proof. exact (eq_refl (term182 A s f _94456)). Qed.
Lemma lem7078482 {A : Type'} (_94458 : A) (s : A -> Prop) (f : A -> real) (h1 : term140 A s f) : term183 A s f _94458.
Proof. exact (@lem7078472 A s f h1 _94458). Qed.
Lemma lem7078483 {A : Type'} (s : A -> Prop) (f : A -> real) (_94458 : A) : (term183 A s f _94458) = (term131 A s f _94458).
Proof. exact (eq_refl (term183 A s f _94458)). Qed.
Lemma lem7078486 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7078498 {A : Type'} (s : A -> Prop) (h1 : term171 A s) : term171 A s.
Proof. exact (h1). Qed.
Lemma lem7078506 {A : Type'} (_94456 : A) (s : A -> Prop) (f : A -> real) (h1 : term41 A s f) : term116 A s f _94456.
Proof. exact (EQ_MP (@lem7078477 A s f _94456) (@lem7078476 A _94456 s f h1)). Qed.
Lemma lem7078514 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) (h1 : term120 A s f x') : term184 A f x'.
Proof. exact (proj2 (@lem7078369 A s f x' h1)). Qed.
Lemma lem7078524 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem7078526 {A : Type'} (f : A -> real) (x : A) (h1 : term43 A f x) : term43 A f x.
Proof. exact (h1). Qed.
Lemma lem7078532 {A : Type'} (_94458 : A) (s : A -> Prop) (f : A -> real) (h1 : term140 A s f) : term131 A s f _94458.
Proof. exact (EQ_MP (@lem7078483 A s f _94458) (@lem7078482 A _94458 s f h1)). Qed.
Lemma lem7078534 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7078535 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term185 A s.
Proof. exact (fun h0 : term171 A s => @lem7078534 A s h1). Qed.
Lemma lem7078537 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7078538 {A : Type'} (s : A -> Prop) : (term185 A s) = (@FINITE A s).
Proof. exact (@lem7078537 (@FINITE A s)). Qed.
Lemma lem7078539 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem7078538 A s) (@lem7078535 A s h1)). Qed.
Lemma lem7078542 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7078544 {A : Type'} (s : A -> Prop) : (term171 A s) = (term187 A s).
Proof. exact (@lem7078542 (@FINITE A s)). Qed.
Lemma lem7078547 {A : Type'} (s : A -> Prop) (h1 : term171 A s) : term187 A s.
Proof. exact (EQ_MP (@lem7078544 A s) (@lem7078498 A s h1)). Qed.
Lemma lem7078550 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term171 A s) : False.
Proof. exact (@lem7078547 A s h2 (@lem7078539 A s h1)). Qed.
Lemma lem7078551 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term171 A s) : term188.
Proof. exact (fun h0 : ~ False => @lem7078550 A s h1 h2). Qed.
Lemma lem7078553 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7078554 : term188 = False.
Proof. exact (@lem7078553 False). Qed.
Lemma lem7078555 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term171 A s) : False.
Proof. exact (EQ_MP (@lem7078554) (@lem7078551 A s h1 h2)). Qed.
Lemma lem7078557 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) (h1 : term120 A s f x') : @IN A x' s.
Proof. exact (proj1 (@lem7078369 A s f x' h1)). Qed.
Lemma lem7078558 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) (h1 : term120 A s f x') : term189 A x' s.
Proof. exact (fun h0 : term190 A x' s => @lem7078557 A s f x' h1). Qed.
Lemma lem7078560 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7078561 {A : Type'} (x' : A) (s : A -> Prop) : (term189 A x' s) = (@IN A x' s).
Proof. exact (@lem7078560 (@IN A x' s)). Qed.
Lemma lem7078562 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) (h1 : term120 A s f x') : @IN A x' s.
Proof. exact (EQ_MP (@lem7078561 A x' s) (@lem7078558 A s f x' h1)). Qed.
Lemma lem7078568 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7078569 {A : Type'} (f : A -> real) (_94456 : A) (s : A -> Prop) : (term116 A s f _94456) = (term191 A f _94456 s).
Proof. exact (@lem7078568 (term86 A f _94456) (term190 A _94456 s)). Qed.
Lemma lem7078575 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7078576 {A : Type'} (f : A -> real) (_94456 : A) (s : A -> Prop) : (term192 A s f _94456) = (term193 A f _94456 s).
Proof. exact (MK_COMB (@lem7078575) (@lem7078569 A f _94456 s)). Qed.
Lemma lem7078582 {A : Type'} (f : A -> real) (_94456 : A) (s : A -> Prop) : (term191 A f _94456 s) = (term191 A f _94456 s).
Proof. exact (eq_refl (term191 A f _94456 s)). Qed.
Lemma lem7078583 {A : Type'} (f : A -> real) (_94456 : A) (s : A -> Prop) : ((term116 A s f _94456) = (term191 A f _94456 s)) = ((term191 A f _94456 s) = (term191 A f _94456 s)).
Proof. exact (MK_COMB (@lem7078576 A f _94456 s) (@lem7078582 A f _94456 s)). Qed.
Lemma lem7078585 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7078586 (x : Prop) : (x = x) = True.
Proof. exact (@lem7078585 Prop x). Qed.
Lemma lem7078587 {A : Type'} (f : A -> real) (_94456 : A) (s : A -> Prop) : ((term191 A f _94456 s) = (term191 A f _94456 s)) = True.
Proof. exact (@lem7078586 (term191 A f _94456 s)). Qed.
Lemma lem7078588 {A : Type'} (f : A -> real) (_94456 : A) (s : A -> Prop) : ((term116 A s f _94456) = (term191 A f _94456 s)) = True.
Proof. exact (TRANS (@lem7078583 A f _94456 s) (@lem7078587 A f _94456 s)). Qed.
Lemma lem7078589 {A : Type'} (f : A -> real) (_94456 : A) (s : A -> Prop) : True = ((term116 A s f _94456) = (term191 A f _94456 s)).
Proof. exact (SYM (@lem7078588 A f _94456 s)). Qed.
Lemma lem7078590 {A : Type'} (f : A -> real) (_94456 : A) (s : A -> Prop) : (term116 A s f _94456) = (term191 A f _94456 s).
Proof. exact (EQ_MP (@lem7078589 A f _94456 s) (@lem0)). Qed.
Lemma lem7078591 {A : Type'} (_94456 : A) (s : A -> Prop) (f : A -> real) (h1 : term41 A s f) : term191 A f _94456 s.
Proof. exact (EQ_MP (@lem7078590 A f _94456 s) (@lem7078506 A _94456 s f h1)). Qed.
Lemma lem7078593 (b : Prop) (a : Prop) : (a \/ b) = (term194 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7078594 {A : Type'} (s : A -> Prop) (f : A -> real) (_94456 : A) : (term191 A f _94456 s) = (term195 A s f _94456).
Proof. exact (@lem7078593 (term190 A _94456 s) (term86 A f _94456)). Qed.
Lemma lem7078596 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7078597 {A : Type'} (_94456 : A) (s : A -> Prop) : (term196 A _94456 s) = (@IN A _94456 s).
Proof. exact (@lem7078596 (@IN A _94456 s)). Qed.
Lemma lem7078598 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7078599 {A : Type'} (_94456 : A) (s : A -> Prop) : (term197 A _94456 s) = (term63 A _94456 s).
Proof. exact (MK_COMB (@lem7078598) (@lem7078597 A _94456 s)). Qed.
Lemma lem7078600 {A : Type'} (f : A -> real) (_94456 : A) : (term86 A f _94456) = (term86 A f _94456).
Proof. exact (eq_refl (term86 A f _94456)). Qed.
Lemma lem7078601 {A : Type'} (s : A -> Prop) (f : A -> real) (_94456 : A) : (term195 A s f _94456) = (term88 A s f _94456).
Proof. exact (MK_COMB (@lem7078599 A _94456 s) (@lem7078600 A f _94456)). Qed.
Lemma lem7078602 {A : Type'} (s : A -> Prop) (f : A -> real) (_94456 : A) : (term191 A f _94456 s) = (term88 A s f _94456).
Proof. exact (TRANS (@lem7078594 A s f _94456) (@lem7078601 A s f _94456)). Qed.
Lemma lem7078605 {A : Type'} (_94456 : A) (s : A -> Prop) (f : A -> real) (h1 : term41 A s f) : term88 A s f _94456.
Proof. exact (EQ_MP (@lem7078602 A s f _94456) (@lem7078591 A _94456 s f h1)). Qed.
Lemma lem7078606 {A : Type'} (_94456 : A) (s : A -> Prop) (f : A -> real) (h1 : term41 A s f) : term88 A s f _94456.
Proof. exact (@lem7078605 A _94456 s f h1). Qed.
Lemma lem7078607 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (h1 : term41 A s f) : term88 A s f x'.
Proof. exact (@lem7078606 A x' s f h1). Qed.
Lemma lem7078610 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) (h1 : term41 A s f) (h2 : term120 A s f x') : term86 A f x'.
Proof. exact (@lem7078607 A x' s f h1 (@lem7078562 A s f x' h2)). Qed.
Lemma lem7078611 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) (h1 : term41 A s f) (h2 : term120 A s f x') : term198 A f x'.
Proof. exact (fun h0 : term184 A f x' => @lem7078610 A s f x' h1 h2). Qed.
Lemma lem7078613 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7078614 {A : Type'} (f : A -> real) (x' : A) : (term198 A f x') = (term86 A f x').
Proof. exact (@lem7078613 (term86 A f x')). Qed.
Lemma lem7078615 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) (h1 : term41 A s f) (h2 : term120 A s f x') : term86 A f x'.
Proof. exact (EQ_MP (@lem7078614 A f x') (@lem7078611 A s f x' h1 h2)). Qed.
Lemma lem7078618 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7078620 {A : Type'} (f : A -> real) (x' : A) : (term184 A f x') = (term199 A f x').
Proof. exact (@lem7078618 (term86 A f x')). Qed.
Lemma lem7078623 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) (h1 : term120 A s f x') : term199 A f x'.
Proof. exact (EQ_MP (@lem7078620 A f x') (@lem7078514 A s f x' h1)). Qed.
Lemma lem7078626 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) (h1 : term41 A s f) (h2 : term120 A s f x') : False.
Proof. exact (@lem7078623 A s f x' h2 (@lem7078615 A s f x' h1 h2)). Qed.
Lemma lem7078627 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) (h1 : term41 A s f) (h2 : term120 A s f x') : term188.
Proof. exact (fun h0 : ~ False => @lem7078626 A s f x' h1 h2). Qed.
Lemma lem7078629 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7078630 : term188 = False.
Proof. exact (@lem7078629 False). Qed.
Lemma lem7078631 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) (h1 : term41 A s f) (h2 : term120 A s f x') : False.
Proof. exact (EQ_MP (@lem7078630) (@lem7078627 A s f x' h1 h2)). Qed.
Lemma lem7078633 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem7078634 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : term189 A x s.
Proof. exact (fun h0 : term190 A x s => @lem7078633 A x s h1). Qed.
Lemma lem7078636 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7078637 {A : Type'} (x : A) (s : A -> Prop) : (term189 A x s) = (@IN A x s).
Proof. exact (@lem7078636 (@IN A x s)). Qed.
Lemma lem7078638 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (EQ_MP (@lem7078637 A x s) (@lem7078634 A x s h1)). Qed.
Lemma lem7078640 {A : Type'} (f : A -> real) (x : A) (h1 : term43 A f x) : term43 A f x.
Proof. exact (h1). Qed.
Lemma lem7078641 {A : Type'} (f : A -> real) (x : A) (h1 : term43 A f x) : term200 A f x.
Proof. exact (fun h0 : term201 A f x => @lem7078640 A f x h1). Qed.
Lemma lem7078643 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7078644 {A : Type'} (f : A -> real) (x : A) : (term200 A f x) = (term43 A f x).
Proof. exact (@lem7078643 (term43 A f x)). Qed.
Lemma lem7078645 {A : Type'} (f : A -> real) (x : A) (h1 : term43 A f x) : term43 A f x.
Proof. exact (EQ_MP (@lem7078644 A f x) (@lem7078641 A f x h1)). Qed.
Lemma lem7078647 (a : Prop) (b : Prop) : (term202 a b) = (term203 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem7078648 {A : Type'} (s : A -> Prop) (f : A -> real) (_94458 : A) : (term131 A s f _94458) = (term130 A s f _94458).
Proof. exact (@lem7078647 (@IN A _94458 s) (term43 A f _94458)). Qed.
Lemma lem7078650 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7078651 {A : Type'} (s : A -> Prop) (f : A -> real) (_94458 : A) : (term130 A s f _94458) = (term204 A s f _94458).
Proof. exact (@lem7078650 (term42 A s f _94458)). Qed.
Lemma lem7078652 {A : Type'} (s : A -> Prop) (f : A -> real) (_94458 : A) : (term131 A s f _94458) = (term204 A s f _94458).
Proof. exact (TRANS (@lem7078648 A s f _94458) (@lem7078651 A s f _94458)). Qed.
Lemma lem7078654 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : @IN A x s) (h2 : term43 A f x) : term42 A s f x.
Proof. exact (conj (@lem7078638 A x s h1) (@lem7078645 A f x h2)). Qed.
Lemma lem7078656 {A : Type'} (_94458 : A) (s : A -> Prop) (f : A -> real) (h1 : term140 A s f) : term204 A s f _94458.
Proof. exact (EQ_MP (@lem7078652 A s f _94458) (@lem7078532 A _94458 s f h1)). Qed.
Lemma lem7078657 {A : Type'} (_94458 : A) (s : A -> Prop) (f : A -> real) (h1 : term140 A s f) : term204 A s f _94458.
Proof. exact (@lem7078656 A _94458 s f h1). Qed.
Lemma lem7078658 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (h1 : term140 A s f) : term204 A s f x.
Proof. exact (@lem7078657 A x s f h1). Qed.
Lemma lem7078661 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term140 A s f) (h2 : @IN A x s) (h3 : term43 A f x) : False.
Proof. exact (@lem7078658 A x s f h1 (@lem7078654 A s f x h2 h3)). Qed.
Lemma lem7078662 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term140 A s f) (h2 : @IN A x s) (h3 : term43 A f x) : term188.
Proof. exact (fun h0 : ~ False => @lem7078661 A s f x h1 h2 h3). Qed.
Lemma lem7078664 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7078665 : term188 = False.
Proof. exact (@lem7078664 False). Qed.
Lemma lem7078666 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term140 A s f) (h2 : @IN A x s) (h3 : term43 A f x) : False.
Proof. exact (EQ_MP (@lem7078665) (@lem7078662 A s f x h1 h2 h3)). Qed.
Lemma lem7078667 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term140 A s f) (h2 : @IN A x s) (h3 : term43 A f x) : (term43 A f x) = False.
Proof. exact (prop_ext (fun h4 : term43 A f x => @lem7078666 A s f x h1 h2 h3) (fun h4 : False => @lem7078526 A f x h3)). Qed.
Lemma lem7078668 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term140 A s f) (h2 : @IN A x s) (h3 : term43 A f x) : False.
Proof. exact (EQ_MP (@lem7078667 A s f x h1 h2 h3) (@lem7078526 A f x h3)). Qed.
Lemma lem7078669 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term140 A s f) (h2 : @IN A x s) (h3 : term43 A f x) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h4 : @IN A x s => @lem7078668 A s f x h1 h2 h3) (fun h4 : False => @lem7078524 A x s h2)). Qed.
Lemma lem7078670 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term140 A s f) (h2 : @IN A x s) (h3 : term43 A f x) : False.
Proof. exact (EQ_MP (@lem7078669 A s f x h1 h2 h3) (@lem7078524 A x s h2)). Qed.
Lemma lem7078671 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term171 A s) : (term171 A s) = False.
Proof. exact (prop_ext (fun h3 : term171 A s => @lem7078555 A s h1 h2) (fun h3 : False => @lem7078498 A s h2)). Qed.
Lemma lem7078672 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term171 A s) : False.
Proof. exact (EQ_MP (@lem7078671 A s h1 h2) (@lem7078498 A s h2)). Qed.
Lemma lem7078673 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term171 A s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem7078672 A s h1 h2) (fun h3 : False => @lem7078486 A s h1)). Qed.
Lemma lem7078674 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term171 A s) : False.
Proof. exact (EQ_MP (@lem7078673 A s h1 h2) (@lem7078486 A s h1)). Qed.
Lemma lem7078675 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term140 A s f) (h2 : @IN A x s) (h3 : term43 A f x) : (term43 A f x) = False.
Proof. exact (prop_ext (fun h4 : term43 A f x => @lem7078670 A s f x h1 h2 h3) (fun h4 : False => @lem7078459 A f x h3)). Qed.
Lemma lem7078676 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term140 A s f) (h2 : @IN A x s) (h3 : term43 A f x) : False.
Proof. exact (EQ_MP (@lem7078675 A s f x h1 h2 h3) (@lem7078459 A f x h3)). Qed.
Lemma lem7078677 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term140 A s f) (h2 : @IN A x s) (h3 : term43 A f x) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h4 : @IN A x s => @lem7078676 A s f x h1 h2 h3) (fun h4 : False => @lem7078455 A x s h2)). Qed.
Lemma lem7078678 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term140 A s f) (h2 : @IN A x s) (h3 : term43 A f x) : False.
Proof. exact (EQ_MP (@lem7078677 A s f x h1 h2 h3) (@lem7078455 A x s h2)). Qed.
Lemma lem7078679 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term171 A s) : (term171 A s) = False.
Proof. exact (prop_ext (fun h3 : term171 A s => @lem7078674 A s h1 h2) (fun h3 : False => @lem7078401 A s h2)). Qed.
Lemma lem7078680 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term171 A s) : False.
Proof. exact (EQ_MP (@lem7078679 A s h1 h2) (@lem7078401 A s h2)). Qed.
Lemma lem7078681 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term171 A s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem7078680 A s h1 h2) (fun h3 : False => @lem7078376 A s h1)). Qed.
Lemma lem7078682 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term171 A s) : False.
Proof. exact (EQ_MP (@lem7078681 A s h1 h2) (@lem7078376 A s h1)). Qed.
Lemma lem7078683 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term140 A s f) (h2 : @IN A x s) (h3 : term43 A f x) : (term140 A s f) = False.
Proof. exact (prop_ext (fun h4 : term140 A s f => @lem7078678 A s f x h1 h2 h3) (fun h4 : False => @lem7078472 A s f h1)). Qed.
Lemma lem7078684 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term140 A s f) (h2 : @IN A x s) (h3 : term43 A f x) : False.
Proof. exact (EQ_MP (@lem7078683 A s f x h1 h2 h3) (@lem7078472 A s f h1)). Qed.
Lemma lem7078685 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term140 A s f) (h2 : @IN A x s) (h3 : term43 A f x) : (term43 A f x) = False.
Proof. exact (prop_ext (fun h4 : term43 A f x => @lem7078684 A s f x h1 h2 h3) (fun h4 : False => @lem7078459 A f x h3)). Qed.
Lemma lem7078686 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term140 A s f) (h2 : @IN A x s) (h3 : term43 A f x) : False.
Proof. exact (EQ_MP (@lem7078685 A s f x h1 h2 h3) (@lem7078459 A f x h3)). Qed.
Lemma lem7078687 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term140 A s f) (h2 : @IN A x s) (h3 : term43 A f x) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h4 : @IN A x s => @lem7078686 A s f x h1 h2 h3) (fun h4 : False => @lem7078455 A x s h2)). Qed.
Lemma lem7078688 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term140 A s f) (h2 : @IN A x s) (h3 : term43 A f x) : False.
Proof. exact (EQ_MP (@lem7078687 A s f x h1 h2 h3) (@lem7078455 A x s h2)). Qed.
Lemma lem7078689 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term171 A s) : (term171 A s) = False.
Proof. exact (prop_ext (fun h3 : term171 A s => @lem7078682 A s h1 h2) (fun h3 : False => @lem7078401 A s h2)). Qed.
Lemma lem7078690 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term171 A s) : False.
Proof. exact (EQ_MP (@lem7078689 A s h1 h2) (@lem7078401 A s h2)). Qed.
Lemma lem7078691 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term171 A s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem7078690 A s h1 h2) (fun h3 : False => @lem7078376 A s h1)). Qed.
Lemma lem7078692 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term171 A s) : False.
Proof. exact (EQ_MP (@lem7078691 A s h1 h2) (@lem7078376 A s h1)). Qed.
Lemma lem7078693 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @IN A x s) (h3 : term162 A x' s f) (h4 : term43 A f x) : False.
Proof. exact (or_elim (@lem7078368 A x' s f h3) (fun h0 : term120 A s f x' => @lem7078631 A s f x' h1 h0) (fun h0 : term140 A s f => @lem7078688 A s f x h0 h2 h4)). Qed.
Lemma lem7078694 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term178 A x' s f) (h5 : term43 A f x) : False.
Proof. exact (or_elim (@lem7078366 A x' s f h4) (fun h0 : term171 A s => @lem7078692 A s h2 h0) (fun h0 : term162 A x' s f => @lem7078693 A x' s f x h1 h3 h0 h5)). Qed.
Lemma lem7078695 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term178 A x' s f) (h5 : term43 A f x) : (term178 A x' s f) = False.
Proof. exact (prop_ext (fun h6 : term178 A x' s f => @lem7078694 A x' s f x h1 h2 h3 h4 h5) (fun h6 : False => @lem7078366 A x' s f h4)). Qed.
Lemma lem7078696 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term178 A x' s f) (h5 : term43 A f x) : False.
Proof. exact (EQ_MP (@lem7078695 A x' s f x h1 h2 h3 h4 h5) (@lem7078366 A x' s f h4)). Qed.
Lemma lem7078697 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term178 A x' s f) (h5 : term43 A f x) : (term43 A f x) = False.
Proof. exact (prop_ext (fun h6 : term43 A f x => @lem7078696 A x' s f x h1 h2 h3 h4 h5) (fun h6 : False => @lem7078307 A f x h5)). Qed.
Lemma lem7078698 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term178 A x' s f) (h5 : term43 A f x) : False.
Proof. exact (EQ_MP (@lem7078697 A x' s f x h1 h2 h3 h4 h5) (@lem7078307 A f x h5)). Qed.
Lemma lem7078699 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term178 A x' s f) (h5 : term43 A f x) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h6 : @IN A x s => @lem7078698 A x' s f x h1 h2 h3 h4 h5) (fun h6 : False => @lem7078295 A x s h3)). Qed.
Lemma lem7078700 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term178 A x' s f) (h5 : term43 A f x) : False.
Proof. exact (EQ_MP (@lem7078699 A x' s f x h1 h2 h3 h4 h5) (@lem7078295 A x s h3)). Qed.
Lemma lem7078701 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term178 A x' s f) (h5 : term43 A f x) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h6 : @FINITE A s => @lem7078700 A x' s f x h1 h2 h3 h4 h5) (fun h6 : False => @lem7078264 A s h2)). Qed.
Lemma lem7078702 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term178 A x' s f) (h5 : term43 A f x) : False.
Proof. exact (EQ_MP (@lem7078701 A x' s f x h1 h2 h3 h4 h5) (@lem7078264 A s h2)). Qed.
Lemma lem7078703 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : term115 A s f) (h4 : @IN A x s) (h5 : term43 A f x) : False.
Proof. exact (ex_elim (@lem7078259 A s f h3) (fun x' : A => fun h0 : term180 A s f x' => @lem7078702 A x' s f x h1 h2 h4 h0 h5)). Qed.
Lemma lem7078704 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : term115 A s f) (h4 : @IN A x s) (h5 : term43 A f x) : (term43 A f x) = False.
Proof. exact (prop_ext (fun h6 : term43 A f x => @lem7078703 A s f x h1 h2 h3 h4 h5) (fun h6 : False => @lem7078067 A f x h5)). Qed.
Lemma lem7078705 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : term115 A s f) (h4 : @IN A x s) (h5 : term43 A f x) : False.
Proof. exact (EQ_MP (@lem7078704 A s f x h1 h2 h3 h4 h5) (@lem7078067 A f x h5)). Qed.
Lemma lem7078706 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : term115 A s f) (h4 : @IN A x s) (h5 : term43 A f x) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h6 : @IN A x s => @lem7078705 A s f x h1 h2 h3 h4 h5) (fun h6 : False => @lem7078061 A x s h4)). Qed.
Lemma lem7078707 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : term115 A s f) (h4 : @IN A x s) (h5 : term43 A f x) : False.
Proof. exact (EQ_MP (@lem7078706 A s f x h1 h2 h3 h4 h5) (@lem7078061 A x s h4)). Qed.
Lemma lem7078708 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : term115 A s f) (h4 : @IN A x s) (h5 : term43 A f x) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h6 : @FINITE A s => @lem7078707 A s f x h1 h2 h3 h4 h5) (fun h6 : False => @lem7077992 A s h2)). Qed.
Lemma lem7078709 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : term115 A s f) (h4 : @IN A x s) (h5 : term43 A f x) : False.
Proof. exact (EQ_MP (@lem7078708 A s f x h1 h2 h3 h4 h5) (@lem7077992 A s h2)). Qed.
Lemma lem7078710 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : term115 A s f) (h4 : @IN A x s) (h5 : term43 A f x) : (term115 A s f) = False.
Proof. exact (prop_ext (fun h6 : term115 A s f => @lem7078709 A s f x h1 h2 h3 h4 h5) (fun h6 : False => @lem7077986 A s f h3)). Qed.
Lemma lem7078711 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : term115 A s f) (h4 : @IN A x s) (h5 : term43 A f x) : False.
Proof. exact (EQ_MP (@lem7078710 A s f x h1 h2 h3 h4 h5) (@lem7077986 A s f h3)). Qed.
Lemma lem7078712 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term43 A f x) : term114 A s f.
Proof. exact (fun h0 : term115 A s f => @lem7078711 A s f x h1 h2 h0 h3 h4). Qed.
Lemma lem7078713 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term43 A f x) : term38 A s f.
Proof. exact (EQ_MP (@lem7077985 A s f) (@lem7078712 A s f x h1 h2 h3 h4)). Qed.
Lemma lem7078714 {A : Type'} (f : A -> real) (x : A) (s : A -> Prop) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : @IN A x s) : term104 A x s f.
Proof. exact (fun h0 : term43 A f x => @lem7078713 A s f x h1 h2 h3 h0). Qed.
Lemma lem7078715 {A : Type'} (x : A) (f : A -> real) (s : A -> Prop) (h1 : term41 A s f) (h2 : @FINITE A s) : term105 A x s f.
Proof. exact (fun h0 : @IN A x s => @lem7078714 A f x s h1 h2 h0). Qed.
Lemma lem7078716 {A : Type'} (x : A) (f : A -> real) (s : A -> Prop) (h1 : @FINITE A s) : term106 A x s f.
Proof. exact (fun h0 : term41 A s f => @lem7078715 A x f s h0 h1). Qed.
Lemma lem7078717 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : term107 A x s f.
Proof. exact (fun h0 : @FINITE A s => @lem7078716 A x f s h0). Qed.
Lemma lem7078722 {A : Type'} (s : A -> Prop) (f : A -> real) : term109 A s f.
Proof. exact (fun x : A => @lem7078717 A x s f). Qed.
Lemma lem7078727 {A : Type'} (f : A -> real) : term111 A f.
Proof. exact (fun s : A -> Prop => @lem7078722 A s f). Qed.
Lemma lem7078732 {A : Type'} : term113 A.
Proof. exact (fun f : A -> real => @lem7078727 A f). Qed.
Lemma lem7078733 {A : Type'} : term81 A.
Proof. exact (EQ_MP (@lem7077977 A) (@lem7078732 A)). Qed.
Lemma lem7078734 {A : Type'} (f : A -> real) : term205 A f.
Proof. exact (@lem7078733 A f). Qed.
Lemma lem7078735 {A : Type'} (f : A -> real) : (term205 A f) = (term77 A f).
Proof. exact (eq_refl (term205 A f)). Qed.
Lemma lem7078736 {A : Type'} (f : A -> real) : term77 A f.
Proof. exact (EQ_MP (@lem7078735 A f) (@lem7078734 A f)). Qed.
Lemma lem7078737 {A : Type'} (f : A -> real) (s : A -> Prop) : term206 A f s.
Proof. exact (@lem7078736 A f s). Qed.
Lemma lem7078738 {A : Type'} (s : A -> Prop) (f : A -> real) : (term206 A f s) = (term73 A s f).
Proof. exact (eq_refl (term206 A f s)). Qed.
Lemma lem7078739 {A : Type'} (s : A -> Prop) (f : A -> real) : term73 A s f.
Proof. exact (EQ_MP (@lem7078738 A s f) (@lem7078737 A f s)). Qed.
Lemma lem7078740 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : term207 A s f x.
Proof. exact (@lem7078739 A s f x). Qed.
Lemma lem7078741 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term207 A s f x) = (term54 A x s f).
Proof. exact (eq_refl (term207 A s f x)). Qed.
Lemma lem7078742 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : term54 A x s f.
Proof. exact (EQ_MP (@lem7078741 A x s f) (@lem7078740 A s f x)). Qed.
Lemma lem7078744 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : term54 A x s f.
Proof. exact (@lem7077689 A x s f (@lem7078742 A x s f)). Qed.
Lemma lem7078745 {A : Type'} (x : A) (f : A -> real) (s : A -> Prop) (h1 : @FINITE A s) : term67 A x s f.
Proof. exact (@lem7078744 A x s f (@lem7077643 A s h1)). Qed.
Lemma lem7078746 {A : Type'} (x : A) (f : A -> real) (s : A -> Prop) (h1 : term41 A s f) (h2 : @FINITE A s) : term64 A x s f.
Proof. exact (@lem7078745 A x f s h2 (@lem7077645 A s f h1)). Qed.
Lemma lem7078747 {A : Type'} (f : A -> real) (x : A) (s : A -> Prop) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : @IN A x s) : term61 A x s f.
Proof. exact (@lem7078746 A x f s h1 h2 (@lem7077648 A x s h3)). Qed.
Lemma lem7078748 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term43 A f x) : term52 A s f.
Proof. exact (@lem7078747 A f x s h1 h2 h3 (@lem7077647 A f x h4)). Qed.
Lemma lem7078749 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : term53 A s f) (h4 : @IN A x s) (h5 : term43 A f x) : False.
Proof. exact (@lem7078748 A s f x h1 h2 h4 h5 (@lem7077673 A s f h3)). Qed.
Lemma lem7078750 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : term53 A s f) (h4 : @IN A x s) (h5 : term43 A f x) : (term53 A s f) = False.
Proof. exact (prop_ext (fun h6 : term53 A s f => @lem7078749 A s f x h1 h2 h3 h4 h5) (fun h6 : False => @lem7077673 A s f h3)). Qed.
Lemma lem7078751 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : term53 A s f) (h4 : @IN A x s) (h5 : term43 A f x) : False.
Proof. exact (EQ_MP (@lem7078750 A s f x h1 h2 h3 h4 h5) (@lem7077673 A s f h3)). Qed.
Lemma lem7078752 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term43 A f x) : term52 A s f.
Proof. exact (fun h0 : term53 A s f => @lem7078751 A s f x h1 h2 h0 h3 h4). Qed.
Lemma lem7078753 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term43 A f x) : term51 A s f.
Proof. exact (EQ_MP (@lem7077672 A s f) (@lem7078752 A s f x h1 h2 h3 h4)). Qed.
Lemma lem7078754 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term43 A f x) : term208 A s f.
Proof. exact (@lem7077668 A s f (@lem7078753 A s f x h1 h2 h3 h4)). Qed.
Lemma lem7078755 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term43 A f x) : term209 A s f.
Proof. exact (conj (@lem7077664 A s) (@lem7078754 A s f x h1 h2 h3 h4)). Qed.
Lemma lem7078756 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term43 A f x) : term210 A s f.
Proof. exact (ex_intro (term211 A s f) (term19 A s) (@lem7078755 A s f x h1 h2 h3 h4)). Qed.
Lemma lem7078757 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term43 A f x) : term212 A s f.
Proof. exact (@lem7077651 A s f (@lem7078756 A s f x h1 h2 h3 h4)). Qed.
Lemma lem7078758 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term38 A s f) : term39 A s f.
Proof. exact (proj2 (@lem7077641 A s f h1)). Qed.
Lemma lem7078759 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term38 A s f) : @FINITE A s.
Proof. exact (proj1 (@lem7077641 A s f h1)). Qed.
Lemma lem7078760 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term39 A s f) : term40 A s f.
Proof. exact (proj2 (@lem7077642 A s f h1)). Qed.
Lemma lem7078761 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term39 A s f) : term41 A s f.
Proof. exact (proj1 (@lem7077642 A s f h1)). Qed.
Lemma lem7078762 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term42 A s f x) : term43 A f x.
Proof. exact (proj2 (@lem7077646 A s f x h1)). Qed.
Lemma lem7078763 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term42 A s f x) : @IN A x s.
Proof. exact (proj1 (@lem7077646 A s f x h1)). Qed.
Lemma lem7078764 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term43 A f x) : (term43 A f x) = (term212 A s f).
Proof. exact (prop_ext (fun h5 : term43 A f x => @lem7078757 A s f x h1 h2 h3 h4) (fun h5 : term212 A s f => @lem7077647 A f x h4)). Qed.
Lemma lem7078765 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term43 A f x) : term212 A s f.
Proof. exact (EQ_MP (@lem7078764 A s f x h1 h2 h3 h4) (@lem7077647 A f x h4)). Qed.
Lemma lem7078766 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term43 A f x) : (@IN A x s) = (term212 A s f).
Proof. exact (prop_ext (fun h5 : @IN A x s => @lem7078765 A s f x h1 h2 h3 h4) (fun h5 : term212 A s f => @lem7077648 A x s h3)). Qed.
Lemma lem7078767 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term43 A f x) : term212 A s f.
Proof. exact (EQ_MP (@lem7078766 A s f x h1 h2 h3 h4) (@lem7077648 A x s h3)). Qed.
Lemma lem7078768 {A : Type'} (f : A -> real) (x : A) (s : A -> Prop) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : term42 A s f x) (h4 : @IN A x s) : (term43 A f x) = (term212 A s f).
Proof. exact (prop_ext (fun h5 : term43 A f x => @lem7078767 A s f x h1 h2 h4 h5) (fun h5 : term212 A s f => @lem7078762 A s f x h3)). Qed.
Lemma lem7078769 {A : Type'} (f : A -> real) (x : A) (s : A -> Prop) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : term42 A s f x) (h4 : @IN A x s) : term212 A s f.
Proof. exact (EQ_MP (@lem7078768 A f x s h1 h2 h3 h4) (@lem7078762 A s f x h3)). Qed.
Lemma lem7078770 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : term42 A s f x) : (@IN A x s) = (term212 A s f).
Proof. exact (prop_ext (fun h4 : @IN A x s => @lem7078769 A f x s h1 h2 h3 h4) (fun h4 : term212 A s f => @lem7078763 A s f x h3)). Qed.
Lemma lem7078771 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : term42 A s f x) : term212 A s f.
Proof. exact (EQ_MP (@lem7078770 A s f x h1 h2 h3) (@lem7078763 A s f x h3)). Qed.
Lemma lem7078772 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term41 A s f) (h2 : term40 A s f) (h3 : @FINITE A s) : term212 A s f.
Proof. exact (ex_elim (@lem7077644 A s f h2) (fun x : A => fun h0 : term100 A s f x => @lem7078771 A s f x h1 h3 h0)). Qed.
Lemma lem7078773 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term41 A s f) (h2 : term40 A s f) (h3 : @FINITE A s) : (term41 A s f) = (term212 A s f).
Proof. exact (prop_ext (fun h4 : term41 A s f => @lem7078772 A f s h1 h2 h3) (fun h4 : term212 A s f => @lem7077645 A s f h1)). Qed.
Lemma lem7078774 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term41 A s f) (h2 : term40 A s f) (h3 : @FINITE A s) : term212 A s f.
Proof. exact (EQ_MP (@lem7078773 A f s h1 h2 h3) (@lem7077645 A s f h1)). Qed.
Lemma lem7078775 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : term39 A s f) : (term40 A s f) = (term212 A s f).
Proof. exact (prop_ext (fun h4 : term40 A s f => @lem7078774 A f s h1 h4 h2) (fun h4 : term212 A s f => @lem7078760 A s f h3)). Qed.
Lemma lem7078776 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term41 A s f) (h2 : @FINITE A s) (h3 : term39 A s f) : term212 A s f.
Proof. exact (EQ_MP (@lem7078775 A s f h1 h2 h3) (@lem7078760 A s f h3)). Qed.
Lemma lem7078777 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : @FINITE A s) (h2 : term39 A s f) : (term41 A s f) = (term212 A s f).
Proof. exact (prop_ext (fun h3 : term41 A s f => @lem7078776 A s f h3 h1 h2) (fun h3 : term212 A s f => @lem7078761 A s f h2)). Qed.
Lemma lem7078778 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : @FINITE A s) (h2 : term39 A s f) : term212 A s f.
Proof. exact (EQ_MP (@lem7078777 A s f h1 h2) (@lem7078761 A s f h2)). Qed.
Lemma lem7078779 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : @FINITE A s) (h2 : term39 A s f) : (@FINITE A s) = (term212 A s f).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem7078778 A s f h1 h2) (fun h3 : term212 A s f => @lem7077643 A s h1)). Qed.
Lemma lem7078780 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : @FINITE A s) (h2 : term39 A s f) : term212 A s f.
Proof. exact (EQ_MP (@lem7078779 A s f h1 h2) (@lem7077643 A s h1)). Qed.
Lemma lem7078781 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : @FINITE A s) (h2 : term38 A s f) : (term39 A s f) = (term212 A s f).
Proof. exact (prop_ext (fun h3 : term39 A s f => @lem7078780 A s f h1 h3) (fun h3 : term212 A s f => @lem7078758 A s f h2)). Qed.
Lemma lem7078782 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : @FINITE A s) (h2 : term38 A s f) : term212 A s f.
Proof. exact (EQ_MP (@lem7078781 A s f h1 h2) (@lem7078758 A s f h2)). Qed.
Lemma lem7078783 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term38 A s f) : (@FINITE A s) = (term212 A s f).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem7078782 A s f h2 h1) (fun h2 : term212 A s f => @lem7078759 A s f h1)). Qed.
Lemma lem7078784 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term38 A s f) : term212 A s f.
Proof. exact (EQ_MP (@lem7078783 A s f h1) (@lem7078759 A s f h1)). Qed.
Lemma lem7078785 {A : Type'} (s : A -> Prop) (f : A -> real) : term213 A s f.
Proof. exact (fun h0 : term38 A s f => @lem7078784 A s f h0). Qed.
Lemma lem7078790 {A : Type'} (f : A -> real) : term214 A f.
Proof. exact (fun s : A -> Prop => @lem7078785 A s f). Qed.
Lemma lem7078795 {A : Type'} : term215 A.
Proof. exact (fun f : A -> real => @lem7078790 A f). Qed.
