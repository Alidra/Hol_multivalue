Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import BIJECTIONS_HAS_SIZE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import HAS_SIZE_IMAGE_INJ_spec.
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
Require Import thm18928_spec.
Require Import thm18929_spec.
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
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem5092663 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem5092664 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term1 A B f.
Proof. exact (@lem5092663 A B h1 f). Qed.
Lemma lem5092665 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem5092666 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term2 A B f.
Proof. exact (EQ_MP (@lem5092665 A B f) (@lem5092664 A B f h1)). Qed.
Lemma lem5092667 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term0 A B) : term3 A B f s.
Proof. exact (@lem5092666 A B f h1 s). Qed.
Lemma lem5092668 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term3 A B f s) = (term4 A B f s).
Proof. exact (eq_refl (term3 A B f s)). Qed.
Lemma lem5092669 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term0 A B) : term4 A B f s.
Proof. exact (EQ_MP (@lem5092668 A B f s) (@lem5092667 A B f s h1)). Qed.
Lemma lem5092670 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term0 A B) : term5 A B f s n.
Proof. exact (@lem5092669 A B f s h1 n). Qed.
Lemma lem5092671 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term5 A B f s n) = (term6 A B f s n).
Proof. exact (eq_refl (term5 A B f s n)). Qed.
Lemma lem5092672 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term0 A B) : term6 A B f s n.
Proof. exact (EQ_MP (@lem5092671 A B f s n) (@lem5092670 A B f s n h1)). Qed.
Lemma lem5092673 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term7 A B f s n) : term7 A B f s n.
Proof. exact (h1). Qed.
Lemma lem5092674 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term0 A B) (h2 : term7 A B f s n) : term8 A B f s n.
Proof. exact (@lem5092672 A B f s n h1 (@lem5092673 A B f s n h2)). Qed.
Lemma lem5092675 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term7 A B f s n) : term9 A B f s n.
Proof. exact (fun h0 : term0 A B => @lem5092674 A B f s n h0 h1). Qed.
Lemma lem5092676 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem5092677 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term0 A B) (h2 : term7 A B f s n) : term8 A B f s n.
Proof. exact (@lem5092675 A B f s n h2 (@lem5092676 A B h1)). Qed.
Lemma lem5092678 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term0 A B) : term6 A B f s n.
Proof. exact (fun h0 : term7 A B f s n => @lem5092677 A B f s n h1 h0). Qed.
Lemma lem5092679 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term0 A B) : term4 A B f s.
Proof. exact (fun n : nat => @lem5092678 A B f s n h1). Qed.
Lemma lem5092680 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term2 A B f.
Proof. exact (fun s : A -> Prop => @lem5092679 A B f s h1). Qed.
Lemma lem5092681 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (fun f : A -> B => @lem5092680 A B f h1). Qed.
Lemma lem5092682 {A B : Type'} : term10 A B.
Proof. exact (fun h0 : term0 A B => @lem5092681 A B h0). Qed.
Lemma lem5092683 {A B : Type'} : term0 A B.
Proof. exact (@lem5092682 A B (@lem4004559 A B)). Qed.
Lemma lem5092684 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (@lem5092683 A B f). Qed.
Lemma lem5092685 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem5092686 {A B : Type'} (f : A -> B) : term2 A B f.
Proof. exact (EQ_MP (@lem5092685 A B f) (@lem5092684 A B f)). Qed.
Lemma lem5092687 {A B : Type'} (f : A -> B) (s : A -> Prop) : term3 A B f s.
Proof. exact (@lem5092686 A B f s). Qed.
Lemma lem5092688 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term3 A B f s) = (term4 A B f s).
Proof. exact (eq_refl (term3 A B f s)). Qed.
Lemma lem5092689 {A B : Type'} (f : A -> B) (s : A -> Prop) : term4 A B f s.
Proof. exact (EQ_MP (@lem5092688 A B f s) (@lem5092687 A B f s)). Qed.
Lemma lem5092690 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : term5 A B f s n.
Proof. exact (@lem5092689 A B f s n). Qed.
Lemma lem5092691 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term5 A B f s n) = (term6 A B f s n).
Proof. exact (eq_refl (term5 A B f s n)). Qed.
Lemma lem5092693 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (s : A -> Prop) (n : nat) (h1 : term11 A B t f g s n) : term11 A B t f g s n.
Proof. exact (h1). Qed.
Lemma lem5092694 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (s : A -> Prop) (n : nat) (h1 : term12 A B t f g s n) : term12 A B t f g s n.
Proof. exact (h1). Qed.
Lemma lem5092695 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term13 A B s t g f) : term13 A B s t g f.
Proof. exact (h1). Qed.
Lemma lem5092696 {A : Type'} (s : A -> Prop) (n : nat) (h1 : @HAS_SIZE A s n) : @HAS_SIZE A s n.
Proof. exact (h1). Qed.
Lemma lem5092697 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term14 A B t s f g) : term14 A B t s f g.
Proof. exact (h1). Qed.
Lemma lem5092698 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : t = (@IMAGE A B f s)) : t = (@IMAGE A B f s).
Proof. exact (h1). Qed.
Lemma lem5092699 {B : Type'} (n : nat) : (term15 B n) = (term15 B n).
Proof. exact (eq_refl (term15 B n)). Qed.
Lemma lem5092700 {A B : Type'} (n : nat) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : t = (@IMAGE A B f s)) : (term16 B n t) = (term17 A B n f s).
Proof. exact (MK_COMB (@lem5092699 B n) (@lem5092698 A B t f s h1)). Qed.
Lemma lem5092701 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term17 A B n f s) = (term8 A B f s n).
Proof. exact (eq_refl (term17 A B n f s)). Qed.
Lemma lem5092702 {B : Type'} (n : nat) (t : B -> Prop) : (term18 B n t) = (term18 B n t).
Proof. exact (eq_refl (term18 B n t)). Qed.
Lemma lem5092703 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (n : nat) : ((term16 B n t) = (term17 A B n f s)) = ((term16 B n t) = (term8 A B f s n)).
Proof. exact (MK_COMB (@lem5092702 B n t) (@lem5092701 A B f s n)). Qed.
Lemma lem5092704 {B : Type'} (t : B -> Prop) (n : nat) : (term16 B n t) = (@HAS_SIZE B t n).
Proof. exact (eq_refl (term16 B n t)). Qed.
Lemma lem5092705 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5092706 {B : Type'} (t : B -> Prop) (n : nat) : (term18 B n t) = (term19 B t n).
Proof. exact (MK_COMB (@lem5092705) (@lem5092704 B t n)). Qed.
Lemma lem5092707 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term8 A B f s n) = (term8 A B f s n).
Proof. exact (eq_refl (term8 A B f s n)). Qed.
Lemma lem5092708 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (n : nat) : ((term16 B n t) = (term8 A B f s n)) = ((@HAS_SIZE B t n) = (term8 A B f s n)).
Proof. exact (MK_COMB (@lem5092706 B t n) (@lem5092707 A B f s n)). Qed.
Lemma lem5092709 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (n : nat) : ((term16 B n t) = (term17 A B n f s)) = ((@HAS_SIZE B t n) = (term8 A B f s n)).
Proof. exact (TRANS (@lem5092703 A B t f s n) (@lem5092708 A B t f s n)). Qed.
Lemma lem5092710 {A B : Type'} (n : nat) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : t = (@IMAGE A B f s)) : (@HAS_SIZE B t n) = (term8 A B f s n).
Proof. exact (EQ_MP (@lem5092709 A B t f s n) (@lem5092700 A B n t f s h1)). Qed.
Lemma lem5092711 {A B : Type'} (n : nat) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : t = (@IMAGE A B f s)) : (term8 A B f s n) = (@HAS_SIZE B t n).
Proof. exact (SYM (@lem5092710 A B n t f s h1)). Qed.
Lemma lem5092712 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term20 A B s g f) = (term20 A B s g f).
Proof. exact (eq_refl (term20 A B s g f)). Qed.
Lemma lem5092713 {A B : Type'} (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : t = (@IMAGE A B f s)) : (term21 A B s g f t) = (term22 A B g f s).
Proof. exact (MK_COMB (@lem5092712 A B s g f) (@lem5092698 A B t f s h1)). Qed.
Lemma lem5092714 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term22 A B g f s) = (term23 A B s g f).
Proof. exact (eq_refl (term22 A B g f s)). Qed.
Lemma lem5092715 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (t : B -> Prop) : (term24 A B s g f t) = (term24 A B s g f t).
Proof. exact (eq_refl (term24 A B s g f t)). Qed.
Lemma lem5092716 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> A) (f : A -> B) : ((term21 A B s g f t) = (term22 A B g f s)) = ((term21 A B s g f t) = (term23 A B s g f)).
Proof. exact (MK_COMB (@lem5092715 A B s g f t) (@lem5092714 A B s g f)). Qed.
Lemma lem5092717 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term21 A B s g f t) = (term13 A B s t g f).
Proof. exact (eq_refl (term21 A B s g f t)). Qed.
Lemma lem5092718 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5092719 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term24 A B s g f t) = (term25 A B s t g f).
Proof. exact (MK_COMB (@lem5092718) (@lem5092717 A B s t g f)). Qed.
Lemma lem5092720 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term23 A B s g f) = (term23 A B s g f).
Proof. exact (eq_refl (term23 A B s g f)). Qed.
Lemma lem5092721 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> A) (f : A -> B) : ((term21 A B s g f t) = (term23 A B s g f)) = ((term13 A B s t g f) = (term23 A B s g f)).
Proof. exact (MK_COMB (@lem5092719 A B s t g f) (@lem5092720 A B s g f)). Qed.
Lemma lem5092722 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> A) (f : A -> B) : ((term21 A B s g f t) = (term22 A B g f s)) = ((term13 A B s t g f) = (term23 A B s g f)).
Proof. exact (TRANS (@lem5092716 A B t s g f) (@lem5092721 A B t s g f)). Qed.
Lemma lem5092723 {A B : Type'} (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : t = (@IMAGE A B f s)) : (term13 A B s t g f) = (term23 A B s g f).
Proof. exact (EQ_MP (@lem5092722 A B t s g f) (@lem5092713 A B g t f s h1)). Qed.
Lemma lem5092724 {A B : Type'} (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term13 A B s t g f) (h2 : t = (@IMAGE A B f s)) : term23 A B s g f.
Proof. exact (EQ_MP (@lem5092723 A B g t f s h2) (@lem5092695 A B s t g f h1)). Qed.
Lemma lem5092725 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term26 A B s f g) = (term26 A B s f g).
Proof. exact (eq_refl (term26 A B s f g)). Qed.
Lemma lem5092726 {A B : Type'} (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : t = (@IMAGE A B f s)) : (term27 A B s f g t) = (term28 A B g f s).
Proof. exact (MK_COMB (@lem5092725 A B s f g) (@lem5092698 A B t f s h1)). Qed.
Lemma lem5092727 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term28 A B g f s) = (term29 A B s f g).
Proof. exact (eq_refl (term28 A B g f s)). Qed.
Lemma lem5092728 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (t : B -> Prop) : (term30 A B s f g t) = (term30 A B s f g t).
Proof. exact (eq_refl (term30 A B s f g t)). Qed.
Lemma lem5092729 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term27 A B s f g t) = (term28 A B g f s)) = ((term27 A B s f g t) = (term29 A B s f g)).
Proof. exact (MK_COMB (@lem5092728 A B s f g t) (@lem5092727 A B s f g)). Qed.
Lemma lem5092730 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term27 A B s f g t) = (term14 A B t s f g).
Proof. exact (eq_refl (term27 A B s f g t)). Qed.
Lemma lem5092731 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5092732 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term30 A B s f g t) = (term31 A B t s f g).
Proof. exact (MK_COMB (@lem5092731) (@lem5092730 A B t s f g)). Qed.
Lemma lem5092733 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term29 A B s f g) = (term29 A B s f g).
Proof. exact (eq_refl (term29 A B s f g)). Qed.
Lemma lem5092734 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term27 A B s f g t) = (term29 A B s f g)) = ((term14 A B t s f g) = (term29 A B s f g)).
Proof. exact (MK_COMB (@lem5092732 A B t s f g) (@lem5092733 A B s f g)). Qed.
Lemma lem5092735 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term27 A B s f g t) = (term28 A B g f s)) = ((term14 A B t s f g) = (term29 A B s f g)).
Proof. exact (TRANS (@lem5092729 A B t s f g) (@lem5092734 A B t s f g)). Qed.
Lemma lem5092736 {A B : Type'} (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : t = (@IMAGE A B f s)) : (term14 A B t s f g) = (term29 A B s f g).
Proof. exact (EQ_MP (@lem5092735 A B t s f g) (@lem5092726 A B g t f s h1)). Qed.
Lemma lem5092737 {A B : Type'} (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term14 A B t s f g) (h2 : t = (@IMAGE A B f s)) : term29 A B s f g.
Proof. exact (EQ_MP (@lem5092736 A B g t f s h2) (@lem5092697 A B t s f g h1)). Qed.
Lemma lem5092751 {A : Type'} (s : A -> Prop) (n : nat) (h1 : @HAS_SIZE A s n) : @HAS_SIZE A s n.
Proof. exact (h1). Qed.
Lemma lem5092762 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term13 A B s t g f) (h2 : term14 A B t s f g) : term32 A B s t g f.
Proof. exact (conj (@lem5092697 A B t s f g h2) (@lem5092695 A B s t g f h1)). Qed.
Lemma lem5092763 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (s : A -> Prop) (n : nat) (h1 : term13 A B s t g f) (h2 : term14 A B t s f g) (h3 : @HAS_SIZE A s n) : term33 A B n s t g f.
Proof. exact (conj (@lem5092696 A s n h3) (@lem5092762 A B t s f g h1 h2)). Qed.
Lemma lem5092797 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term34 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5092798 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term34 B s t).
Proof. exact (@lem5092797 B s t). Qed.
Lemma lem5092799 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (t = (@IMAGE A B f s)) = (term35 A B t f s).
Proof. exact (@lem5092798 B t (@IMAGE A B f s)). Qed.
Lemma lem5092808 {A B : Type'} (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term36 A B n s t g f) = (term36 A B n s t g f).
Proof. exact (eq_refl (term36 A B n s t g f)). Qed.
Lemma lem5092809 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term37 A B n g t f s) = (term38 A B n g t f s).
Proof. exact (MK_COMB (@lem5092808 A B n s t g f) (@lem5092799 A B t f s)). Qed.
Lemma lem5092812 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term38 A B n g t f s) = (term37 A B n g t f s).
Proof. exact (SYM (@lem5092809 A B n g t f s)). Qed.
Lemma lem5092826 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5092827 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5092826 B P x). Qed.
Lemma lem5092828 {B : Type'} (t : B -> Prop) (y : B) : (@IN B y t) = (t y).
Proof. exact (@lem5092827 B t y). Qed.
Lemma lem5092829 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5092830 {B : Type'} (t : B -> Prop) (y : B) : (term39 B y t) = (term40 B t y).
Proof. exact (MK_COMB (@lem5092829) (@lem5092828 B t y)). Qed.
Lemma lem5092834 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5092835 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5092834 A P x). Qed.
Lemma lem5092836 {A B : Type'} (s : A -> Prop) (g : B -> A) (y : B) : (term41 A B g y s) = (term42 A B s g y).
Proof. exact (@lem5092835 A s (g y)). Qed.
Lemma lem5092837 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5092838 {A B : Type'} (s : A -> Prop) (g : B -> A) (y : B) : (term43 A B g y s) = (term44 A B s g y).
Proof. exact (MK_COMB (@lem5092837) (@lem5092836 A B s g y)). Qed.
Lemma lem5092841 {A B : Type'} (f : A -> B) (g : B -> A) (y : B) : ((term45 A B f g y) = y) = ((term45 A B f g y) = y).
Proof. exact (eq_refl ((term45 A B f g y) = y)). Qed.
Lemma lem5092842 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term46 A B s f g y) = (term47 A B s f g y).
Proof. exact (MK_COMB (@lem5092838 A B s g y) (@lem5092841 A B f g y)). Qed.
Lemma lem5092845 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term48 A B t s f g y) = (term49 A B t s f g y).
Proof. exact (MK_COMB (@lem5092830 B t y) (@lem5092842 A B s f g y)). Qed.
Lemma lem5092848 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term50 A B t s f g) = (term51 A B t s f g).
Proof. exact (fun_ext (fun y : B => @lem5092845 A B t s f g y)). Qed.
Lemma lem5092849 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5092850 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term14 A B t s f g) = (term52 A B t s f g).
Proof. exact (MK_COMB (@lem5092849 B) (@lem5092848 A B t s f g)). Qed.
Lemma lem5092855 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5092856 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term53 A B t s f g) = (term54 A B t s f g).
Proof. exact (MK_COMB (@lem5092855) (@lem5092850 A B t s f g)). Qed.
Lemma lem5092864 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5092865 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5092864 A P x). Qed.
Lemma lem5092866 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5092865 A s x). Qed.
Lemma lem5092867 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5092868 {A : Type'} (s : A -> Prop) (x : A) : (term39 A x s) = (term40 A s x).
Proof. exact (MK_COMB (@lem5092867) (@lem5092866 A s x)). Qed.
Lemma lem5092872 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5092873 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5092872 B P x). Qed.
Lemma lem5092874 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) : (term55 A B f x t) = (term56 A B t f x).
Proof. exact (@lem5092873 B t (f x)). Qed.
Lemma lem5092875 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5092876 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) : (term57 A B f x t) = (term58 A B t f x).
Proof. exact (MK_COMB (@lem5092875) (@lem5092874 A B t f x)). Qed.
Lemma lem5092879 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : ((term59 A B g f x) = x) = ((term59 A B g f x) = x).
Proof. exact (eq_refl ((term59 A B g f x) = x)). Qed.
Lemma lem5092880 {A B : Type'} (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term60 A B t g f x) = (term61 A B t g f x).
Proof. exact (MK_COMB (@lem5092876 A B t f x) (@lem5092879 A B g f x)). Qed.
Lemma lem5092883 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term62 A B s t g f x) = (term63 A B s t g f x).
Proof. exact (MK_COMB (@lem5092868 A s x) (@lem5092880 A B t g f x)). Qed.
Lemma lem5092886 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term64 A B s t g f) = (term65 A B s t g f).
Proof. exact (fun_ext (fun x : A => @lem5092883 A B s t g f x)). Qed.
Lemma lem5092887 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5092888 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term13 A B s t g f) = (term66 A B s t g f).
Proof. exact (MK_COMB (@lem5092887 A) (@lem5092886 A B s t g f)). Qed.
Lemma lem5092893 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term32 A B s t g f) = (term67 A B s t g f).
Proof. exact (MK_COMB (@lem5092856 A B t s f g) (@lem5092888 A B s t g f)). Qed.
Lemma lem5092896 {A : Type'} (s : A -> Prop) (n : nat) : (term68 A s n) = (term68 A s n).
Proof. exact (eq_refl (term68 A s n)). Qed.
Lemma lem5092897 {A B : Type'} (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term33 A B n s t g f) = (term69 A B n s t g f).
Proof. exact (MK_COMB (@lem5092896 A s n) (@lem5092893 A B s t g f)). Qed.
Lemma lem5092900 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5092901 {A B : Type'} (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term36 A B n s t g f) = (term70 A B n s t g f).
Proof. exact (MK_COMB (@lem5092900) (@lem5092897 A B n s t g f)). Qed.
Lemma lem5092909 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5092910 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5092909 B P x). Qed.
Lemma lem5092911 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem5092910 B t x). Qed.
Lemma lem5092912 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5092913 {B : Type'} (t : B -> Prop) (x : B) : (term71 B x t) = (term72 B t x).
Proof. exact (MK_COMB (@lem5092912) (@lem5092911 B t x)). Qed.
Lemma lem5092915 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term73 A B y f s) = (term74 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem5092916 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term73 A B y f s) = (term74 A B y f s).
Proof. exact (@lem5092915 A B y f s). Qed.
Lemma lem5092917 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term73 A B x f s) = (term74 A B x f s).
Proof. exact (@lem5092916 A B x f s). Qed.
Lemma lem5092927 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5092928 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5092927 A P x). Qed.
Lemma lem5092929 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5092928 A s x). Qed.
Lemma lem5092930 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term75 A B x f x') = (term75 A B x f x').
Proof. exact (eq_refl (term75 A B x f x')). Qed.
Lemma lem5092931 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term76 A B x f x' s) = (term77 A B x f s x').
Proof. exact (MK_COMB (@lem5092930 A B x f x') (@lem5092929 A s x')). Qed.
Lemma lem5092934 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term78 A B x f s) = (term79 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5092931 A B x f s x')). Qed.
Lemma lem5092935 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5092936 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term74 A B x f s) = (term80 A B x f s).
Proof. exact (MK_COMB (@lem5092935 A) (@lem5092934 A B x f s)). Qed.
Lemma lem5092941 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term73 A B x f s) = (term80 A B x f s).
Proof. exact (TRANS (@lem5092917 A B x f s) (@lem5092936 A B x f s)). Qed.
Lemma lem5092942 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : ((@IN B x t) = (term73 A B x f s)) = ((t x) = (term80 A B x f s)).
Proof. exact (MK_COMB (@lem5092913 B t x) (@lem5092941 A B x f s)). Qed.
Lemma lem5092945 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term81 A B t f s) = (term82 A B t f s).
Proof. exact (fun_ext (fun x : B => @lem5092942 A B t x f s)). Qed.
Lemma lem5092946 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5092947 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term35 A B t f s) = (term83 A B t f s).
Proof. exact (MK_COMB (@lem5092946 B) (@lem5092945 A B t f s)). Qed.
Lemma lem5092952 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term38 A B n g t f s) = (term84 A B n g t f s).
Proof. exact (MK_COMB (@lem5092901 A B n s t g f) (@lem5092947 A B t f s)). Qed.
Lemma lem5092955 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term84 A B n g t f s) = (term38 A B n g t f s).
Proof. exact (SYM (@lem5092952 A B n g t f s)). Qed.
Lemma lem5092957 (p : Prop) : p = (term85 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5092958 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term84 A B n g t f s) = (term86 A B n g t f s).
Proof. exact (@lem5092957 (term84 A B n g t f s)). Qed.
Lemma lem5092959 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term86 A B n g t f s) = (term84 A B n g t f s).
Proof. exact (SYM (@lem5092958 A B n g t f s)). Qed.
Lemma lem5092960 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term87 A B n g t f s) : term87 A B n g t f s.
Proof. exact (h1). Qed.
Lemma lem5092963 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term86 A B n g t f s) : term86 A B n g t f s.
Proof. exact (h1). Qed.
Lemma lem5092964 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term88 A B n g t f s.
Proof. exact (fun h0 : term86 A B n g t f s => @lem5092963 A B n g t f s h0). Qed.
Lemma lem5092965 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term88 A B n g t f s) : term88 A B n g t f s.
Proof. exact (h1). Qed.
Lemma lem5092966 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term86 A B n g t f s) : term86 A B n g t f s.
Proof. exact (h1). Qed.
Lemma lem5092967 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term86 A B n g t f s) (h2 : term88 A B n g t f s) : term86 A B n g t f s.
Proof. exact (@lem5092965 A B n g t f s h2 (@lem5092966 A B n g t f s h1)). Qed.
Lemma lem5092968 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term86 A B n g t f s) : term89 A B n g t f s.
Proof. exact (fun h0 : term88 A B n g t f s => @lem5092967 A B n g t f s h1 h0). Qed.
Lemma lem5092969 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term88 A B n g t f s) : term88 A B n g t f s.
Proof. exact (h1). Qed.
Lemma lem5092970 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term86 A B n g t f s) (h2 : term88 A B n g t f s) : term86 A B n g t f s.
Proof. exact (@lem5092968 A B n g t f s h1 (@lem5092969 A B n g t f s h2)). Qed.
Lemma lem5092971 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term88 A B n g t f s) : term88 A B n g t f s.
Proof. exact (fun h0 : term86 A B n g t f s => @lem5092970 A B n g t f s h0 h1). Qed.
Lemma lem5092972 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term90 A B n g t f s.
Proof. exact (fun h0 : term88 A B n g t f s => @lem5092971 A B n g t f s h0). Qed.
Lemma lem5092975 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term88 A B n g t f s.
Proof. exact (@lem5092972 A B n g t f s (@lem5092964 A B n g t f s)). Qed.
Lemma lem5092976 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term88 A B n g t f s.
Proof. exact (@lem5092975 A B n g t f s). Qed.
Lemma lem5092998 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5092999 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term86 A B n g t f s) = (term91 A B n g t f s).
Proof. exact (@lem5092998 (term87 A B n g t f s)). Qed.
Lemma lem5093001 (t : Prop) : (term92 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5093002 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term91 A B n g t f s) = (term84 A B n g t f s).
Proof. exact (@lem5093001 (term84 A B n g t f s)). Qed.
Lemma lem5093005 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term86 A B n g t f s) = (term84 A B n g t f s).
Proof. exact (TRANS (@lem5092999 A B n g t f s) (@lem5093002 A B n g t f s)). Qed.
Lemma lem5093064 {A B : Type'} (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term93 A B g t f s) = (term94 A B g t f s).
Proof. exact (fun_ext (fun n : nat => @lem5093005 A B n g t f s)). Qed.
Lemma lem5093065 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5093066 {A B : Type'} (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term95 A B g t f s) = (term96 A B g t f s).
Proof. exact (MK_COMB (@lem5093065) (@lem5093064 A B g t f s)). Qed.
Lemma lem5093071 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term97 A B t f s) = (term98 A B t f s).
Proof. exact (fun_ext (fun g : B -> A => @lem5093066 A B g t f s)). Qed.
Lemma lem5093072 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem5093073 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term99 A B t f s) = (term100 A B t f s).
Proof. exact (MK_COMB (@lem5093072 A B) (@lem5093071 A B t f s)). Qed.
Lemma lem5093078 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term101 A B f s) = (term102 A B f s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5093073 A B t f s)). Qed.
Lemma lem5093079 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5093080 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term103 A B f s) = (term104 A B f s).
Proof. exact (MK_COMB (@lem5093079 B) (@lem5093078 A B f s)). Qed.
Lemma lem5093085 {A B : Type'} (s : A -> Prop) : (term105 A B s) = (term106 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem5093080 A B f s)). Qed.
Lemma lem5093086 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5093087 {A B : Type'} (s : A -> Prop) : (term107 A B s) = (term108 A B s).
Proof. exact (MK_COMB (@lem5093086 A B) (@lem5093085 A B s)). Qed.
Lemma lem5093092 {A B : Type'} : (term109 A B) = (term110 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5093087 A B s)). Qed.
Lemma lem5093093 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5093102 {A B : Type'} : (term111 A B) = (term112 A B).
Proof. exact (MK_COMB (@lem5093093 A) (@lem5093092 A B)). Qed.
Lemma lem5093107 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term77 A B x f s x') = (term77 A B x f s x').
Proof. exact (eq_refl (term77 A B x f s x')). Qed.
Lemma lem5093108 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term79 A B x f s) = (term79 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5093107 A B x f s x')). Qed.
Lemma lem5093109 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5093110 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term80 A B x f s) = (term80 A B x f s).
Proof. exact (MK_COMB (@lem5093109 A) (@lem5093108 A B x f s)). Qed.
Lemma lem5093113 {B : Type'} (t : B -> Prop) (x : B) : (term72 B t x) = (term72 B t x).
Proof. exact (eq_refl (term72 B t x)). Qed.
Lemma lem5093114 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : ((t x) = (term80 A B x f s)) = ((t x) = (term80 A B x f s)).
Proof. exact (MK_COMB (@lem5093113 B t x) (@lem5093110 A B x f s)). Qed.
Lemma lem5093115 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term82 A B t f s) = (term82 A B t f s).
Proof. exact (fun_ext (fun x : B => @lem5093114 A B t x f s)). Qed.
Lemma lem5093116 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5093117 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term83 A B t f s) = (term83 A B t f s).
Proof. exact (MK_COMB (@lem5093116 B) (@lem5093115 A B t f s)). Qed.
Lemma lem5093126 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term63 A B s t g f x) = (term63 A B s t g f x).
Proof. exact (eq_refl (term63 A B s t g f x)). Qed.
Lemma lem5093127 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term65 A B s t g f) = (term65 A B s t g f).
Proof. exact (fun_ext (fun x : A => @lem5093126 A B s t g f x)). Qed.
Lemma lem5093128 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5093129 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term66 A B s t g f) = (term66 A B s t g f).
Proof. exact (MK_COMB (@lem5093128 A) (@lem5093127 A B s t g f)). Qed.
Lemma lem5093138 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term49 A B t s f g y) = (term49 A B t s f g y).
Proof. exact (eq_refl (term49 A B t s f g y)). Qed.
Lemma lem5093139 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term51 A B t s f g) = (term51 A B t s f g).
Proof. exact (fun_ext (fun y : B => @lem5093138 A B t s f g y)). Qed.
Lemma lem5093140 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5093141 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term52 A B t s f g) = (term52 A B t s f g).
Proof. exact (MK_COMB (@lem5093140 B) (@lem5093139 A B t s f g)). Qed.
Lemma lem5093142 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5093143 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term54 A B t s f g) = (term54 A B t s f g).
Proof. exact (MK_COMB (@lem5093142) (@lem5093141 A B t s f g)). Qed.
Lemma lem5093144 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term67 A B s t g f) = (term67 A B s t g f).
Proof. exact (MK_COMB (@lem5093143 A B t s f g) (@lem5093129 A B s t g f)). Qed.
Lemma lem5093147 {A : Type'} (s : A -> Prop) (n : nat) : (term68 A s n) = (term68 A s n).
Proof. exact (eq_refl (term68 A s n)). Qed.
Lemma lem5093148 {A B : Type'} (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term69 A B n s t g f) = (term69 A B n s t g f).
Proof. exact (MK_COMB (@lem5093147 A s n) (@lem5093144 A B s t g f)). Qed.
Lemma lem5093149 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5093150 {A B : Type'} (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term70 A B n s t g f) = (term70 A B n s t g f).
Proof. exact (MK_COMB (@lem5093149) (@lem5093148 A B n s t g f)). Qed.
Lemma lem5093151 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term84 A B n g t f s) = (term84 A B n g t f s).
Proof. exact (MK_COMB (@lem5093150 A B n s t g f) (@lem5093117 A B t f s)). Qed.
Lemma lem5093152 {A B : Type'} (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term94 A B g t f s) = (term94 A B g t f s).
Proof. exact (fun_ext (fun n : nat => @lem5093151 A B n g t f s)). Qed.
Lemma lem5093153 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5093154 {A B : Type'} (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term96 A B g t f s) = (term96 A B g t f s).
Proof. exact (MK_COMB (@lem5093153) (@lem5093152 A B g t f s)). Qed.
Lemma lem5093155 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term98 A B t f s) = (term98 A B t f s).
Proof. exact (fun_ext (fun g : B -> A => @lem5093154 A B g t f s)). Qed.
Lemma lem5093156 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem5093157 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term100 A B t f s) = (term100 A B t f s).
Proof. exact (MK_COMB (@lem5093156 A B) (@lem5093155 A B t f s)). Qed.
Lemma lem5093158 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term102 A B f s) = (term102 A B f s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5093157 A B t f s)). Qed.
Lemma lem5093159 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5093160 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term104 A B f s) = (term104 A B f s).
Proof. exact (MK_COMB (@lem5093159 B) (@lem5093158 A B f s)). Qed.
Lemma lem5093161 {A B : Type'} (s : A -> Prop) : (term106 A B s) = (term106 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem5093160 A B f s)). Qed.
Lemma lem5093162 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5093163 {A B : Type'} (s : A -> Prop) : (term108 A B s) = (term108 A B s).
Proof. exact (MK_COMB (@lem5093162 A B) (@lem5093161 A B s)). Qed.
Lemma lem5093164 {A B : Type'} : (term110 A B) = (term110 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5093163 A B s)). Qed.
Lemma lem5093165 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5093166 {A B : Type'} : (term112 A B) = (term112 A B).
Proof. exact (MK_COMB (@lem5093165 A) (@lem5093164 A B)). Qed.
Lemma lem5093239 {A B : Type'} : (term111 A B) = (term112 A B).
Proof. exact (TRANS (@lem5093102 A B) (@lem5093166 A B)). Qed.
Lemma lem5093240 {A B : Type'} : (term112 A B) = (term111 A B).
Proof. exact (SYM (@lem5093239 A B)). Qed.
Lemma lem5093241 {A B : Type'} (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term69 A B n s t g f.
Proof. exact (h1). Qed.
Lemma lem5093243 (p : Prop) : p = (term85 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5093244 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : ((t x) = (term80 A B x f s)) = (term113 A B t x f s).
Proof. exact (@lem5093243 ((t x) = (term80 A B x f s))). Qed.
Lemma lem5093245 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term113 A B t x f s) = ((t x) = (term80 A B x f s)).
Proof. exact (SYM (@lem5093244 A B t x f s)). Qed.
Lemma lem5093246 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term114 A B t x f s) : term114 A B t x f s.
Proof. exact (h1). Qed.
Lemma lem5093258 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term49 A B t s f g y) = (term115 A B t s f g y).
Proof. exact (@lem17265 (t y) (term47 A B s f g y)). Qed.
Lemma lem5093259 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term51 A B t s f g) = (term116 A B t s f g).
Proof. exact (fun_ext (fun y : B => @lem5093258 A B t s f g y)). Qed.
Lemma lem5093260 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5093261 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term52 A B t s f g) = (term117 A B t s f g).
Proof. exact (MK_COMB (@lem5093260 B) (@lem5093259 A B t s f g)). Qed.
Lemma lem5093272 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term63 A B s t g f x) = (term118 A B s t g f x).
Proof. exact (@lem17265 (s x) (term61 A B t g f x)). Qed.
Lemma lem5093273 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term65 A B s t g f) = (term119 A B s t g f).
Proof. exact (fun_ext (fun x : A => @lem5093272 A B s t g f x)). Qed.
Lemma lem5093274 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5093275 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term66 A B s t g f) = (term120 A B s t g f).
Proof. exact (MK_COMB (@lem5093274 A) (@lem5093273 A B s t g f)). Qed.
Lemma lem5093276 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5093277 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term54 A B t s f g) = (term121 A B t s f g).
Proof. exact (MK_COMB (@lem5093276) (@lem5093261 A B t s f g)). Qed.
Lemma lem5093278 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term67 A B s t g f) = (term122 A B s t g f).
Proof. exact (MK_COMB (@lem5093277 A B t s f g) (@lem5093275 A B s t g f)). Qed.
Lemma lem5093280 {A : Type'} (s : A -> Prop) (n : nat) : (term68 A s n) = (term68 A s n).
Proof. exact (eq_refl (term68 A s n)). Qed.
Lemma lem5093381 {A B : Type'} (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term69 A B n s t g f) = (term123 A B n s t g f).
Proof. exact (MK_COMB (@lem5093280 A s n) (@lem5093278 A B s t g f)). Qed.
Lemma lem5093382 {A B : Type'} (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term123 A B n s t g f.
Proof. exact (EQ_MP (@lem5093381 A B n s t g f) (@lem5093241 A B n s t g f h1)). Qed.
Lemma lem5093393 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term124 A B x f s x') = (term125 A B x f s x').
Proof. exact (@lem17045 (x = (f x')) (s x')). Qed.
Lemma lem5093396 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term77 A B x f s x') = (term77 A B x f s x').
Proof. exact (eq_refl (term77 A B x f s x')). Qed.
Lemma lem5093397 {A : Type'} (P : A -> Prop) : (term126 A P) = (term127 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem5093398 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term128 A B x f s) = (term129 A B x f s).
Proof. exact (@lem5093397 A (term79 A B x f s)). Qed.
Lemma lem5093399 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term130 A B x f s x') = (term77 A B x f s x').
Proof. exact (eq_refl (term130 A B x f s x')). Qed.
Lemma lem5093400 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5093401 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term131 A B x f s x') = (term124 A B x f s x').
Proof. exact (MK_COMB (@lem5093400) (@lem5093399 A B x f s x')). Qed.
Lemma lem5093402 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term131 A B x f s x') = (term125 A B x f s x').
Proof. exact (TRANS (@lem5093401 A B x f s x') (@lem5093393 A B x f s x')). Qed.
Lemma lem5093403 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term132 A B x f s) = (term133 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5093402 A B x f s x')). Qed.
Lemma lem5093404 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5093405 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term129 A B x f s) = (term134 A B x f s).
Proof. exact (MK_COMB (@lem5093404 A) (@lem5093403 A B x f s)). Qed.
Lemma lem5093406 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term128 A B x f s) = (term134 A B x f s).
Proof. exact (TRANS (@lem5093398 A B x f s) (@lem5093405 A B x f s)). Qed.
Lemma lem5093407 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term79 A B x f s) = (term79 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5093396 A B x f s x')). Qed.
Lemma lem5093408 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5093409 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term80 A B x f s) = (term80 A B x f s).
Proof. exact (MK_COMB (@lem5093408 A) (@lem5093407 A B x f s)). Qed.
Lemma lem5093411 {B : Type'} (t : B -> Prop) (x : B) : (term135 B t x) = (term135 B t x).
Proof. exact (eq_refl (term135 B t x)). Qed.
Lemma lem5093412 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term136 A B t x f s) = (term136 A B t x f s).
Proof. exact (MK_COMB (@lem5093411 B t x) (@lem5093409 A B x f s)). Qed.
Lemma lem5093414 {B : Type'} (t : B -> Prop) (x : B) : (term137 B t x) = (term137 B t x).
Proof. exact (eq_refl (term137 B t x)). Qed.
Lemma lem5093415 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term138 A B t x f s) = (term139 A B t x f s).
Proof. exact (MK_COMB (@lem5093414 B t x) (@lem5093406 A B x f s)). Qed.
Lemma lem5093416 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5093417 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term140 A B t x f s) = (term141 A B t x f s).
Proof. exact (MK_COMB (@lem5093416) (@lem5093415 A B t x f s)). Qed.
Lemma lem5093418 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term142 A B t x f s) = (term143 A B t x f s).
Proof. exact (MK_COMB (@lem5093417 A B t x f s) (@lem5093412 A B t x f s)). Qed.
Lemma lem5093419 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term114 A B t x f s) = (term142 A B t x f s).
Proof. exact (@lem17646 (t x) (term80 A B x f s)). Qed.
Lemma lem5093420 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term114 A B t x f s) = (term143 A B t x f s).
Proof. exact (TRANS (@lem5093419 A B t x f s) (@lem5093418 A B t x f s)). Qed.
Lemma lem5093503 {A : Type'} (P : Prop) (Q : A -> Prop) : (term144 A P Q) = (term145 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5093504 {A : Type'} (P : Prop) (Q : A -> Prop) : (term144 A P Q) = (term145 A P Q).
Proof. exact (@lem5093503 A P Q). Qed.
Lemma lem5093505 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term146 A B t x f s) = (term147 A B t x f s).
Proof. exact (@lem5093504 A (term148 B t x) (term79 A B x f s)). Qed.
Lemma lem5093506 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term130 A B x f s x') = (term77 A B x f s x').
Proof. exact (eq_refl (term130 A B x f s x')). Qed.
Lemma lem5093507 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term149 A B x f s) = (term79 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5093506 A B x f s x')). Qed.
Lemma lem5093508 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5093509 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term150 A B x f s) = (term80 A B x f s).
Proof. exact (MK_COMB (@lem5093508 A) (@lem5093507 A B x f s)). Qed.
Lemma lem5093510 {B : Type'} (t : B -> Prop) (x : B) : (term135 B t x) = (term135 B t x).
Proof. exact (eq_refl (term135 B t x)). Qed.
Lemma lem5093511 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term146 A B t x f s) = (term136 A B t x f s).
Proof. exact (MK_COMB (@lem5093510 B t x) (@lem5093509 A B x f s)). Qed.
Lemma lem5093512 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5093513 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term151 A B t x f s) = (term152 A B t x f s).
Proof. exact (MK_COMB (@lem5093512) (@lem5093511 A B t x f s)). Qed.
Lemma lem5093514 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term130 A B x f s x') = (term77 A B x f s x').
Proof. exact (eq_refl (term130 A B x f s x')). Qed.
Lemma lem5093515 {B : Type'} (t : B -> Prop) (x : B) : (term135 B t x) = (term135 B t x).
Proof. exact (eq_refl (term135 B t x)). Qed.
Lemma lem5093516 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term153 A B t x f s x') = (term154 A B t x f s x').
Proof. exact (MK_COMB (@lem5093515 B t x) (@lem5093514 A B x f s x')). Qed.
Lemma lem5093517 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term155 A B t x f s) = (term156 A B t x f s).
Proof. exact (fun_ext (fun x' : A => @lem5093516 A B t x f s x')). Qed.
Lemma lem5093518 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5093519 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term147 A B t x f s) = (term157 A B t x f s).
Proof. exact (MK_COMB (@lem5093518 A) (@lem5093517 A B t x f s)). Qed.
Lemma lem5093520 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : ((term146 A B t x f s) = (term147 A B t x f s)) = ((term136 A B t x f s) = (term157 A B t x f s)).
Proof. exact (MK_COMB (@lem5093513 A B t x f s) (@lem5093519 A B t x f s)). Qed.
Lemma lem5093521 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term136 A B t x f s) = (term157 A B t x f s).
Proof. exact (EQ_MP (@lem5093520 A B t x f s) (@lem5093505 A B t x f s)). Qed.
Lemma lem5093522 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term141 A B t x f s) = (term141 A B t x f s).
Proof. exact (eq_refl (term141 A B t x f s)). Qed.
Lemma lem5093523 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term143 A B t x f s) = (term158 A B t x f s).
Proof. exact (MK_COMB (@lem5093522 A B t x f s) (@lem5093521 A B t x f s)). Qed.
Lemma lem5093525 {A : Type'} (P : Prop) (Q : A -> Prop) : (term159 A P Q) = (term160 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5093526 {A : Type'} (P : Prop) (Q : A -> Prop) : (term159 A P Q) = (term160 A P Q).
Proof. exact (@lem5093525 A P Q). Qed.
Lemma lem5093527 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term161 A B t x f s) = (term162 A B t x f s).
Proof. exact (@lem5093526 A (term139 A B t x f s) (term156 A B t x f s)). Qed.
Lemma lem5093528 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term163 A B t x f s x') = (term154 A B t x f s x').
Proof. exact (eq_refl (term163 A B t x f s x')). Qed.
Lemma lem5093529 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term164 A B t x f s) = (term156 A B t x f s).
Proof. exact (fun_ext (fun x' : A => @lem5093528 A B t x f s x')). Qed.
Lemma lem5093530 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5093531 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term165 A B t x f s) = (term157 A B t x f s).
Proof. exact (MK_COMB (@lem5093530 A) (@lem5093529 A B t x f s)). Qed.
Lemma lem5093532 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term141 A B t x f s) = (term141 A B t x f s).
Proof. exact (eq_refl (term141 A B t x f s)). Qed.
Lemma lem5093533 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term161 A B t x f s) = (term158 A B t x f s).
Proof. exact (MK_COMB (@lem5093532 A B t x f s) (@lem5093531 A B t x f s)). Qed.
Lemma lem5093534 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5093535 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term166 A B t x f s) = (term167 A B t x f s).
Proof. exact (MK_COMB (@lem5093534) (@lem5093533 A B t x f s)). Qed.
Lemma lem5093536 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term163 A B t x f s x') = (term154 A B t x f s x').
Proof. exact (eq_refl (term163 A B t x f s x')). Qed.
Lemma lem5093537 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term141 A B t x f s) = (term141 A B t x f s).
Proof. exact (eq_refl (term141 A B t x f s)). Qed.
Lemma lem5093538 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term168 A B t x f s x') = (term169 A B t x f s x').
Proof. exact (MK_COMB (@lem5093537 A B t x f s) (@lem5093536 A B t x f s x')). Qed.
Lemma lem5093539 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term170 A B t x f s) = (term171 A B t x f s).
Proof. exact (fun_ext (fun x' : A => @lem5093538 A B t x f s x')). Qed.
Lemma lem5093540 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5093541 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term162 A B t x f s) = (term172 A B t x f s).
Proof. exact (MK_COMB (@lem5093540 A) (@lem5093539 A B t x f s)). Qed.
Lemma lem5093542 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : ((term161 A B t x f s) = (term162 A B t x f s)) = ((term158 A B t x f s) = (term172 A B t x f s)).
Proof. exact (MK_COMB (@lem5093535 A B t x f s) (@lem5093541 A B t x f s)). Qed.
Lemma lem5093543 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term158 A B t x f s) = (term172 A B t x f s).
Proof. exact (EQ_MP (@lem5093542 A B t x f s) (@lem5093527 A B t x f s)). Qed.
Lemma lem5093545 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term143 A B t x f s) = (term172 A B t x f s).
Proof. exact (TRANS (@lem5093523 A B t x f s) (@lem5093543 A B t x f s)). Qed.
Lemma lem5093546 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term114 A B t x f s) = (term172 A B t x f s).
Proof. exact (TRANS (@lem5093420 A B t x f s) (@lem5093545 A B t x f s)). Qed.
Lemma lem5093547 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term114 A B t x f s) : term172 A B t x f s.
Proof. exact (EQ_MP (@lem5093546 A B t x f s) (@lem5093246 A B t x f s h1)). Qed.
Lemma lem5093548 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term169 A B t x f s x') : term169 A B t x f s x'.
Proof. exact (h1). Qed.
Lemma lem5093565 {A B : Type'} (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term61 A B t g f x) = (term61 A B t g f x).
Proof. exact (eq_refl (term61 A B t g f x)). Qed.
Lemma lem5093566 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5093571 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5093572 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem5093571 A Prop f x). Qed.
Lemma lem5093574 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem5093572 A s x). Qed.
Lemma lem5093575 {A : Type'} (s : A -> Prop) (x : A) : (term148 A s x) = (term173 A s x).
Proof. exact (MK_COMB (@lem5093566) (@lem5093574 A s x)). Qed.
Lemma lem5093576 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5093577 {A : Type'} (s : A -> Prop) (x : A) : (term174 A s x) = (term175 A s x).
Proof. exact (MK_COMB (@lem5093576) (@lem5093575 A s x)). Qed.
Lemma lem5093578 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term118 A B s t g f x) = (term176 A B s t g f x).
Proof. exact (MK_COMB (@lem5093577 A s x) (@lem5093565 A B t g f x)). Qed.
Lemma lem5093579 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term119 A B s t g f) = (term177 A B s t g f).
Proof. exact (fun_ext (fun x : A => @lem5093578 A B s t g f x)). Qed.
Lemma lem5093580 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5093581 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term120 A B s t g f) = (term178 A B s t g f).
Proof. exact (MK_COMB (@lem5093580 A) (@lem5093579 A B s t g f)). Qed.
Lemma lem5093590 {A B : Type'} (f : A -> B) (g : B -> A) (y : B) : ((term45 A B f g y) = y) = ((term45 A B f g y) = y).
Proof. exact (eq_refl ((term45 A B f g y) = y)). Qed.
Lemma lem5093597 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5093598 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem5093597 A Prop f x). Qed.
Lemma lem5093600 {A B : Type'} (s : A -> Prop) (g : B -> A) (y : B) : (term42 A B s g y) = (term179 A B s g y).
Proof. exact (@lem5093598 A s (g y)). Qed.
Lemma lem5093601 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5093602 {A B : Type'} (s : A -> Prop) (g : B -> A) (y : B) : (term44 A B s g y) = (term180 A B s g y).
Proof. exact (MK_COMB (@lem5093601) (@lem5093600 A B s g y)). Qed.
Lemma lem5093603 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term47 A B s f g y) = (term181 A B s f g y).
Proof. exact (MK_COMB (@lem5093602 A B s g y) (@lem5093590 A B f g y)). Qed.
Lemma lem5093610 {B : Type'} (t : B -> Prop) (y : B) : (term174 B t y) = (term174 B t y).
Proof. exact (eq_refl (term174 B t y)). Qed.
Lemma lem5093611 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term115 A B t s f g y) = (term182 A B t s f g y).
Proof. exact (MK_COMB (@lem5093610 B t y) (@lem5093603 A B s f g y)). Qed.
Lemma lem5093612 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term116 A B t s f g) = (term183 A B t s f g).
Proof. exact (fun_ext (fun y : B => @lem5093611 A B t s f g y)). Qed.
Lemma lem5093613 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5093614 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term117 A B t s f g) = (term184 A B t s f g).
Proof. exact (MK_COMB (@lem5093613 B) (@lem5093612 A B t s f g)). Qed.
Lemma lem5093615 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5093616 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term121 A B t s f g) = (term185 A B t s f g).
Proof. exact (MK_COMB (@lem5093615) (@lem5093614 A B t s f g)). Qed.
Lemma lem5093617 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term122 A B s t g f) = (term186 A B s t g f).
Proof. exact (MK_COMB (@lem5093616 A B t s f g) (@lem5093581 A B s t g f)). Qed.
Lemma lem5093624 {A : Type'} (s : A -> Prop) (n : nat) : (term68 A s n) = (term68 A s n).
Proof. exact (eq_refl (term68 A s n)). Qed.
Lemma lem5093625 {A B : Type'} (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term123 A B n s t g f) = (term187 A B n s t g f).
Proof. exact (MK_COMB (@lem5093624 A s n) (@lem5093617 A B s t g f)). Qed.
Lemma lem5093626 {A B : Type'} (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term187 A B n s t g f.
Proof. exact (EQ_MP (@lem5093625 A B n s t g f) (@lem5093382 A B n s t g f h1)). Qed.
Lemma lem5093631 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5093632 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem5093631 A Prop f x). Qed.
Lemma lem5093634 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (@I (A -> Prop) s x').
Proof. exact (@lem5093632 A s x'). Qed.
Lemma lem5093643 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term75 A B x f x') = (term75 A B x f x').
Proof. exact (eq_refl (term75 A B x f x')). Qed.
Lemma lem5093644 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term77 A B x f s x') = (term188 A B x f s x').
Proof. exact (MK_COMB (@lem5093643 A B x f x') (@lem5093634 A s x')). Qed.
Lemma lem5093651 {B : Type'} (t : B -> Prop) (x : B) : (term135 B t x) = (term135 B t x).
Proof. exact (eq_refl (term135 B t x)). Qed.
Lemma lem5093652 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term154 A B t x f s x') = (term189 A B t x f s x').
Proof. exact (MK_COMB (@lem5093651 B t x) (@lem5093644 A B x f s x')). Qed.
Lemma lem5093653 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5093658 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5093659 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem5093658 A Prop f x). Qed.
Lemma lem5093661 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem5093659 A s x). Qed.
Lemma lem5093662 {A : Type'} (s : A -> Prop) (x : A) : (term148 A s x) = (term173 A s x).
Proof. exact (MK_COMB (@lem5093653) (@lem5093661 A s x)). Qed.
Lemma lem5093673 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term190 A B x f x') = (term190 A B x f x').
Proof. exact (eq_refl (term190 A B x f x')). Qed.
Lemma lem5093674 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term125 A B x f s x') = (term191 A B x f s x').
Proof. exact (MK_COMB (@lem5093673 A B x f x') (@lem5093662 A s x')). Qed.
Lemma lem5093675 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term133 A B x f s) = (term192 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5093674 A B x f s x')). Qed.
Lemma lem5093676 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5093677 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term134 A B x f s) = (term193 A B x f s).
Proof. exact (MK_COMB (@lem5093676 A) (@lem5093675 A B x f s)). Qed.
Lemma lem5093682 {B : Type'} (t : B -> Prop) (x : B) : (term137 B t x) = (term137 B t x).
Proof. exact (eq_refl (term137 B t x)). Qed.
Lemma lem5093683 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term139 A B t x f s) = (term194 A B t x f s).
Proof. exact (MK_COMB (@lem5093682 B t x) (@lem5093677 A B x f s)). Qed.
Lemma lem5093684 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5093685 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term141 A B t x f s) = (term195 A B t x f s).
Proof. exact (MK_COMB (@lem5093684) (@lem5093683 A B t x f s)). Qed.
Lemma lem5093686 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term169 A B t x f s x') = (term196 A B t x f s x').
Proof. exact (MK_COMB (@lem5093685 A B t x f s) (@lem5093652 A B t x f s x')). Qed.
Lemma lem5093687 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term169 A B t x f s x') : term196 A B t x f s x'.
Proof. exact (EQ_MP (@lem5093686 A B t x f s x') (@lem5093548 A B t x f s x' h1)). Qed.
Lemma lem5093688 {A B : Type'} (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term186 A B s t g f.
Proof. exact (proj2 (@lem5093626 A B n s t g f h1)). Qed.
Lemma lem5093690 {A B : Type'} (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term178 A B s t g f.
Proof. exact (proj2 (@lem5093688 A B n s t g f h1)). Qed.
Lemma lem5093691 {A B : Type'} (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term184 A B t s f g.
Proof. exact (proj1 (@lem5093688 A B n s t g f h1)). Qed.
Lemma lem5093692 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term194 A B t x f s) : term194 A B t x f s.
Proof. exact (h1). Qed.
Lemma lem5093693 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term189 A B t x f s x') : term189 A B t x f s x'.
Proof. exact (h1). Qed.
Lemma lem5093694 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term194 A B t x f s) : term193 A B x f s.
Proof. exact (proj2 (@lem5093692 A B t x f s h1)). Qed.
Lemma lem5093696 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term189 A B t x f s x') : term188 A B x f s x'.
Proof. exact (proj2 (@lem5093693 A B t x f s x' h1)). Qed.
Lemma lem5093721 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term182 A B t s f g y) = (term197 A B s t f g y).
Proof. exact (@lem19490 (term179 A B s g y) (term148 B t y) ((term45 A B f g y) = y)). Qed.
Lemma lem5093722 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) : (term183 A B t s f g) = (term198 A B s t f g).
Proof. exact (fun_ext (fun y : B => @lem5093721 A B s t f g y)). Qed.
Lemma lem5093723 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5093725 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) : (term184 A B t s f g) = (term199 A B s t f g).
Proof. exact (MK_COMB (@lem5093723 B) (@lem5093722 A B s t f g)). Qed.
Lemma lem5093726 {A B : Type'} (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term199 A B s t f g.
Proof. exact (EQ_MP (@lem5093725 A B s t f g) (@lem5093691 A B n s t g f h1)). Qed.
Lemma lem5093761 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term191 A B x f s x') = (term191 A B x f s x').
Proof. exact (eq_refl (term191 A B x f s x')). Qed.
Lemma lem5093762 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term192 A B x f s) = (term192 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5093761 A B x f s x')). Qed.
Lemma lem5093763 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5093765 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term193 A B x f s) = (term193 A B x f s).
Proof. exact (MK_COMB (@lem5093763 A) (@lem5093762 A B x f s)). Qed.
Lemma lem5093766 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term194 A B t x f s) : term193 A B x f s.
Proof. exact (EQ_MP (@lem5093765 A B x f s) (@lem5093694 A B t x f s h1)). Qed.
Lemma lem5093811 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term176 A B s t g f x) = (term200 A B t s g f x).
Proof. exact (@lem19490 (term56 A B t f x) (term173 A s x) ((term59 A B g f x) = x)). Qed.
Lemma lem5093812 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> A) (f : A -> B) : (term177 A B s t g f) = (term201 A B t s g f).
Proof. exact (fun_ext (fun x : A => @lem5093811 A B t s g f x)). Qed.
Lemma lem5093813 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5093815 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> A) (f : A -> B) : (term178 A B s t g f) = (term202 A B t s g f).
Proof. exact (MK_COMB (@lem5093813 A) (@lem5093812 A B t s g f)). Qed.
Lemma lem5093816 {A B : Type'} (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term202 A B t s g f.
Proof. exact (EQ_MP (@lem5093815 A B t s g f) (@lem5093690 A B n s t g f h1)). Qed.
Lemma lem5093829 {A B : Type'} (_66240 : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term203 A B s t f g _66240.
Proof. exact (@lem5093726 A B n s t g f h1 _66240). Qed.
Lemma lem5093830 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) (_66240 : B) : (term203 A B s t f g _66240) = (term197 A B s t f g _66240).
Proof. exact (eq_refl (term203 A B s t f g _66240)). Qed.
Lemma lem5093831 {A B : Type'} (_66240 : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term197 A B s t f g _66240.
Proof. exact (EQ_MP (@lem5093830 A B s t f g _66240) (@lem5093829 A B _66240 n s t g f h1)). Qed.
Lemma lem5093835 {A B : Type'} (_66242 : A) (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term194 A B t x f s) : term204 A B x f s _66242.
Proof. exact (@lem5093766 A B t x f s h1 _66242). Qed.
Lemma lem5093836 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_66242 : A) : (term204 A B x f s _66242) = (term191 A B x f s _66242).
Proof. exact (eq_refl (term204 A B x f s _66242)). Qed.
Lemma lem5093841 {A B : Type'} (_66244 : A) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term205 A B t s g f _66244.
Proof. exact (@lem5093816 A B n s t g f h1 _66244). Qed.
Lemma lem5093842 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> A) (f : A -> B) (_66244 : A) : (term205 A B t s g f _66244) = (term200 A B t s g f _66244).
Proof. exact (eq_refl (term205 A B t s g f _66244)). Qed.
Lemma lem5093843 {A B : Type'} (_66244 : A) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term200 A B t s g f _66244.
Proof. exact (EQ_MP (@lem5093842 A B t s g f _66244) (@lem5093841 A B _66244 n s t g f h1)). Qed.
Lemma lem5093861 {A B : Type'} (_66242 : A) (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term194 A B t x f s) : term191 A B x f s _66242.
Proof. exact (EQ_MP (@lem5093836 A B x f s _66242) (@lem5093835 A B _66242 t x f s h1)). Qed.
Lemma lem5093879 {A B : Type'} (_66240 : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term206 A B t s g _66240.
Proof. exact (proj1 (@lem5093831 A B _66240 n s t g f h1)). Qed.
Lemma lem5093885 {A B : Type'} (_66240 : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term207 A B t f g _66240.
Proof. exact (proj2 (@lem5093831 A B _66240 n s t g f h1)). Qed.
Lemma lem5093889 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term189 A B t x f s x') : term148 B t x.
Proof. exact (proj1 (@lem5093693 A B t x f s x' h1)). Qed.
Lemma lem5093891 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term189 A B t x f s x') : x = (f x').
Proof. exact (proj1 (@lem5093696 A B t x f s x' h1)). Qed.
Lemma lem5093946 {B : Type'} (t : B -> Prop) : (term208 B t) = (term208 B t).
Proof. exact (eq_refl (term208 B t)). Qed.
Lemma lem5093947 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term189 A B t x f s x') : (term209 B t x) = (term210 A B t f x').
Proof. exact (MK_COMB (@lem5093946 B t) (@lem5093891 A B t x f s x' h1)). Qed.
Lemma lem5093948 {A B : Type'} (t : B -> Prop) (f : A -> B) (x' : A) : (term210 A B t f x') = (term211 A B t f x').
Proof. exact (eq_refl (term210 A B t f x')). Qed.
Lemma lem5093949 {B : Type'} (t : B -> Prop) (x : B) : (term212 B t x) = (term212 B t x).
Proof. exact (eq_refl (term212 B t x)). Qed.
Lemma lem5093950 {A B : Type'} (x : B) (t : B -> Prop) (f : A -> B) (x' : A) : ((term209 B t x) = (term210 A B t f x')) = ((term209 B t x) = (term211 A B t f x')).
Proof. exact (MK_COMB (@lem5093949 B t x) (@lem5093948 A B t f x')). Qed.
Lemma lem5093951 {B : Type'} (t : B -> Prop) (x : B) : (term209 B t x) = (term148 B t x).
Proof. exact (eq_refl (term209 B t x)). Qed.
Lemma lem5093952 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5093953 {B : Type'} (t : B -> Prop) (x : B) : (term212 B t x) = (term213 B t x).
Proof. exact (MK_COMB (@lem5093952) (@lem5093951 B t x)). Qed.
Lemma lem5093954 {A B : Type'} (t : B -> Prop) (f : A -> B) (x' : A) : (term211 A B t f x') = (term211 A B t f x').
Proof. exact (eq_refl (term211 A B t f x')). Qed.
Lemma lem5093955 {A B : Type'} (x : B) (t : B -> Prop) (f : A -> B) (x' : A) : ((term209 B t x) = (term211 A B t f x')) = ((term148 B t x) = (term211 A B t f x')).
Proof. exact (MK_COMB (@lem5093953 B t x) (@lem5093954 A B t f x')). Qed.
Lemma lem5093956 {A B : Type'} (x : B) (t : B -> Prop) (f : A -> B) (x' : A) : ((term209 B t x) = (term210 A B t f x')) = ((term148 B t x) = (term211 A B t f x')).
Proof. exact (TRANS (@lem5093950 A B x t f x') (@lem5093955 A B x t f x')). Qed.
Lemma lem5093957 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term189 A B t x f s x') : (term148 B t x) = (term211 A B t f x').
Proof. exact (EQ_MP (@lem5093956 A B x t f x') (@lem5093947 A B t x f s x' h1)). Qed.
Lemma lem5093958 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term189 A B t x f s x') : term211 A B t f x'.
Proof. exact (EQ_MP (@lem5093957 A B t x f s x' h1) (@lem5093889 A B t x f s x' h1)). Qed.
Lemma lem5093986 {A B : Type'} (_66244 : A) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term214 A B s t f _66244.
Proof. exact (proj1 (@lem5093843 A B _66244 n s t g f h1)). Qed.
Lemma lem5094096 {B : Type'} (x : B) (y : B) (z : B) : term215 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem5094104 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term194 A B t x f s) : t x.
Proof. exact (proj1 (@lem5093692 A B t x f s h1)). Qed.
Lemma lem5094105 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term194 A B t x f s) : term216 B t x.
Proof. exact (fun h0 : term148 B t x => @lem5094104 A B t x f s h1). Qed.
Lemma lem5094107 (p : Prop) : (term217 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5094108 {B : Type'} (t : B -> Prop) (x : B) : (term216 B t x) = (t x).
Proof. exact (@lem5094107 (t x)). Qed.
Lemma lem5094109 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term194 A B t x f s) : t x.
Proof. exact (EQ_MP (@lem5094108 B t x) (@lem5094105 A B t x f s h1)). Qed.
Lemma lem5094115 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5094116 {A B : Type'} (f : A -> B) (g : B -> A) (t : B -> Prop) (_66240 : B) : (term207 A B t f g _66240) = (term218 A B f g t _66240).
Proof. exact (@lem5094115 ((term45 A B f g _66240) = _66240) (term148 B t _66240)). Qed.
Lemma lem5094124 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5094125 {A B : Type'} (f : A -> B) (g : B -> A) (t : B -> Prop) (_66240 : B) : (term219 A B t f g _66240) = (term220 A B f g t _66240).
Proof. exact (MK_COMB (@lem5094124) (@lem5094116 A B f g t _66240)). Qed.
Lemma lem5094133 {A B : Type'} (f : A -> B) (g : B -> A) (t : B -> Prop) (_66240 : B) : (term218 A B f g t _66240) = (term218 A B f g t _66240).
Proof. exact (eq_refl (term218 A B f g t _66240)). Qed.
Lemma lem5094134 {A B : Type'} (f : A -> B) (g : B -> A) (t : B -> Prop) (_66240 : B) : ((term207 A B t f g _66240) = (term218 A B f g t _66240)) = ((term218 A B f g t _66240) = (term218 A B f g t _66240)).
Proof. exact (MK_COMB (@lem5094125 A B f g t _66240) (@lem5094133 A B f g t _66240)). Qed.
Lemma lem5094136 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5094137 (x : Prop) : (x = x) = True.
Proof. exact (@lem5094136 Prop x). Qed.
Lemma lem5094138 {A B : Type'} (f : A -> B) (g : B -> A) (t : B -> Prop) (_66240 : B) : ((term218 A B f g t _66240) = (term218 A B f g t _66240)) = True.
Proof. exact (@lem5094137 (term218 A B f g t _66240)). Qed.
Lemma lem5094139 {A B : Type'} (f : A -> B) (g : B -> A) (t : B -> Prop) (_66240 : B) : ((term207 A B t f g _66240) = (term218 A B f g t _66240)) = True.
Proof. exact (TRANS (@lem5094134 A B f g t _66240) (@lem5094138 A B f g t _66240)). Qed.
Lemma lem5094140 {A B : Type'} (f : A -> B) (g : B -> A) (t : B -> Prop) (_66240 : B) : True = ((term207 A B t f g _66240) = (term218 A B f g t _66240)).
Proof. exact (SYM (@lem5094139 A B f g t _66240)). Qed.
Lemma lem5094141 {A B : Type'} (f : A -> B) (g : B -> A) (t : B -> Prop) (_66240 : B) : (term207 A B t f g _66240) = (term218 A B f g t _66240).
Proof. exact (EQ_MP (@lem5094140 A B f g t _66240) (@lem0)). Qed.
Lemma lem5094142 {A B : Type'} (_66240 : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term218 A B f g t _66240.
Proof. exact (EQ_MP (@lem5094141 A B f g t _66240) (@lem5093885 A B _66240 n s t g f h1)). Qed.
Lemma lem5094144 (b : Prop) (a : Prop) : (a \/ b) = (term221 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5094145 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (_66240 : B) : (term218 A B f g t _66240) = (term222 A B t f g _66240).
Proof. exact (@lem5094144 (term148 B t _66240) ((term45 A B f g _66240) = _66240)). Qed.
Lemma lem5094147 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5094148 {B : Type'} (t : B -> Prop) (_66240 : B) : (term223 B t _66240) = (t _66240).
Proof. exact (@lem5094147 (t _66240)). Qed.
Lemma lem5094149 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5094150 {B : Type'} (t : B -> Prop) (_66240 : B) : (term224 B t _66240) = (term40 B t _66240).
Proof. exact (MK_COMB (@lem5094149) (@lem5094148 B t _66240)). Qed.
Lemma lem5094151 {A B : Type'} (f : A -> B) (g : B -> A) (_66240 : B) : ((term45 A B f g _66240) = _66240) = ((term45 A B f g _66240) = _66240).
Proof. exact (eq_refl ((term45 A B f g _66240) = _66240)). Qed.
Lemma lem5094152 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (_66240 : B) : (term222 A B t f g _66240) = (term225 A B t f g _66240).
Proof. exact (MK_COMB (@lem5094150 B t _66240) (@lem5094151 A B f g _66240)). Qed.
Lemma lem5094153 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (_66240 : B) : (term218 A B f g t _66240) = (term225 A B t f g _66240).
Proof. exact (TRANS (@lem5094145 A B t f g _66240) (@lem5094152 A B t f g _66240)). Qed.
Lemma lem5094156 {A B : Type'} (_66240 : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term225 A B t f g _66240.
Proof. exact (EQ_MP (@lem5094153 A B t f g _66240) (@lem5094142 A B _66240 n s t g f h1)). Qed.
Lemma lem5094157 {A B : Type'} (_66240 : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term225 A B t f g _66240.
Proof. exact (@lem5094156 A B _66240 n s t g f h1). Qed.
Lemma lem5094158 {A B : Type'} (x : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term225 A B t f g x.
Proof. exact (@lem5094157 A B x n s t g f h1). Qed.
Lemma lem5094161 {A B : Type'} (x : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term194 A B t x f s) (h2 : term69 A B n s t g f) : (term45 A B f g x) = x.
Proof. exact (@lem5094158 A B x n s t g f h2 (@lem5094109 A B t x f s h1)). Qed.
Lemma lem5094162 {A B : Type'} (x : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term194 A B t x f s) (h2 : term69 A B n s t g f) : term226 A B f g x.
Proof. exact (fun h0 : term227 A B f g x => @lem5094161 A B x n s t g f h1 h2). Qed.
Lemma lem5094164 (p : Prop) : (term217 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5094165 {A B : Type'} (f : A -> B) (g : B -> A) (x : B) : (term226 A B f g x) = ((term45 A B f g x) = x).
Proof. exact (@lem5094164 ((term45 A B f g x) = x)). Qed.
Lemma lem5094166 {A B : Type'} (x : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term194 A B t x f s) (h2 : term69 A B n s t g f) : (term45 A B f g x) = x.
Proof. exact (EQ_MP (@lem5094165 A B f g x) (@lem5094162 A B x n s t g f h1 h2)). Qed.
Lemma lem5094168 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5094169 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5094168 B x). Qed.
Lemma lem5094170 {A B : Type'} (f : A -> B) (g : B -> A) (x : B) : (term45 A B f g x) = (term45 A B f g x).
Proof. exact (@lem5094169 B (term45 A B f g x)). Qed.
Lemma lem5094171 {A B : Type'} (f : A -> B) (g : B -> A) (x : B) : term228 A B f g x.
Proof. exact (fun h0 : term229 A B f g x => @lem5094170 A B f g x). Qed.
Lemma lem5094173 (p : Prop) : (term217 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5094174 {A B : Type'} (f : A -> B) (g : B -> A) (x : B) : (term228 A B f g x) = ((term45 A B f g x) = (term45 A B f g x)).
Proof. exact (@lem5094173 ((term45 A B f g x) = (term45 A B f g x))). Qed.
Lemma lem5094175 {A B : Type'} (f : A -> B) (g : B -> A) (x : B) : (term45 A B f g x) = (term45 A B f g x).
Proof. exact (EQ_MP (@lem5094174 A B f g x) (@lem5094171 A B f g x)). Qed.
Lemma lem5094193 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5094194 {B : Type'} (y : B) (x : B) (z : B) : (term230 B x y z) = (term231 B y x z).
Proof. exact (@lem5094193 (y = z) (term232 B x z)). Qed.
Lemma lem5094204 {B : Type'} (x : B) (y : B) : (term233 B x y) = (term233 B x y).
Proof. exact (eq_refl (term233 B x y)). Qed.
Lemma lem5094205 {B : Type'} (y : B) (x : B) (z : B) : (term215 B x y z) = (term234 B y x z).
Proof. exact (MK_COMB (@lem5094204 B x y) (@lem5094194 B y x z)). Qed.
Lemma lem5094209 (q : Prop) (p : Prop) (r : Prop) : (term235 p q r) = (term235 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5094210 {B : Type'} (y : B) (x : B) (z : B) : (term234 B y x z) = (term236 B y x z).
Proof. exact (@lem5094209 (y = z) (term232 B x y) (term232 B x z)). Qed.
Lemma lem5094232 {B : Type'} (y : B) (x : B) (z : B) : (term215 B x y z) = (term236 B y x z).
Proof. exact (TRANS (@lem5094205 B y x z) (@lem5094210 B y x z)). Qed.
Lemma lem5094233 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5094234 {B : Type'} (y : B) (x : B) (z : B) : (term237 B x y z) = (term238 B y x z).
Proof. exact (MK_COMB (@lem5094233) (@lem5094232 B y x z)). Qed.
Lemma lem5094256 {B : Type'} (y : B) (x : B) (z : B) : (term236 B y x z) = (term236 B y x z).
Proof. exact (eq_refl (term236 B y x z)). Qed.
Lemma lem5094257 {B : Type'} (y : B) (x : B) (z : B) : ((term215 B x y z) = (term236 B y x z)) = ((term236 B y x z) = (term236 B y x z)).
Proof. exact (MK_COMB (@lem5094234 B y x z) (@lem5094256 B y x z)). Qed.
Lemma lem5094259 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5094260 (x : Prop) : (x = x) = True.
Proof. exact (@lem5094259 Prop x). Qed.
Lemma lem5094261 {B : Type'} (y : B) (x : B) (z : B) : ((term236 B y x z) = (term236 B y x z)) = True.
Proof. exact (@lem5094260 (term236 B y x z)). Qed.
Lemma lem5094262 {B : Type'} (y : B) (x : B) (z : B) : ((term215 B x y z) = (term236 B y x z)) = True.
Proof. exact (TRANS (@lem5094257 B y x z) (@lem5094261 B y x z)). Qed.
Lemma lem5094263 {B : Type'} (y : B) (x : B) (z : B) : True = ((term215 B x y z) = (term236 B y x z)).
Proof. exact (SYM (@lem5094262 B y x z)). Qed.
Lemma lem5094264 {B : Type'} (y : B) (x : B) (z : B) : (term215 B x y z) = (term236 B y x z).
Proof. exact (EQ_MP (@lem5094263 B y x z) (@lem0)). Qed.
Lemma lem5094265 {B : Type'} (y : B) (x : B) (z : B) : term236 B y x z.
Proof. exact (EQ_MP (@lem5094264 B y x z) (@lem5094096 B x y z)). Qed.
Lemma lem5094267 (b : Prop) (a : Prop) : (a \/ b) = (term221 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5094268 {B : Type'} (x : B) (y : B) (z : B) : (term236 B y x z) = (term239 B x y z).
Proof. exact (@lem5094267 (term240 B y x z) (y = z)). Qed.
Lemma lem5094270 (a : Prop) (b : Prop) : (term241 a b) = (term242 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5094271 {B : Type'} (y : B) (x : B) (z : B) : (term243 B y x z) = (term244 B y x z).
Proof. exact (@lem5094270 (term232 B x y) (term232 B x z)). Qed.
Lemma lem5094273 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5094274 {B : Type'} (x : B) (y : B) : (term245 B x y) = (x = y).
Proof. exact (@lem5094273 (x = y)). Qed.
Lemma lem5094275 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5094276 {B : Type'} (x : B) (y : B) : (term246 B x y) = (term247 B x y).
Proof. exact (MK_COMB (@lem5094275) (@lem5094274 B x y)). Qed.
Lemma lem5094278 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5094279 {B : Type'} (x : B) (z : B) : (term245 B x z) = (x = z).
Proof. exact (@lem5094278 (x = z)). Qed.
Lemma lem5094280 {B : Type'} (y : B) (x : B) (z : B) : (term244 B y x z) = (term248 B y x z).
Proof. exact (MK_COMB (@lem5094276 B x y) (@lem5094279 B x z)). Qed.
Lemma lem5094281 {B : Type'} (y : B) (x : B) (z : B) : (term243 B y x z) = (term248 B y x z).
Proof. exact (TRANS (@lem5094271 B y x z) (@lem5094280 B y x z)). Qed.
Lemma lem5094282 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5094283 {B : Type'} (y : B) (x : B) (z : B) : (term249 B y x z) = (term250 B y x z).
Proof. exact (MK_COMB (@lem5094282) (@lem5094281 B y x z)). Qed.
Lemma lem5094284 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5094285 {B : Type'} (x : B) (y : B) (z : B) : (term239 B x y z) = (term251 B x y z).
Proof. exact (MK_COMB (@lem5094283 B y x z) (@lem5094284 B y z)). Qed.
Lemma lem5094286 {B : Type'} (x : B) (y : B) (z : B) : (term236 B y x z) = (term251 B x y z).
Proof. exact (TRANS (@lem5094268 B x y z) (@lem5094285 B x y z)). Qed.
Lemma lem5094288 {A B : Type'} (x : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term194 A B t x f s) (h2 : term69 A B n s t g f) : term252 A B f g x.
Proof. exact (conj (@lem5094166 A B x n s t g f h1 h2) (@lem5094175 A B f g x)). Qed.
Lemma lem5094290 {B : Type'} (x : B) (y : B) (z : B) : term251 B x y z.
Proof. exact (EQ_MP (@lem5094286 B x y z) (@lem5094265 B y x z)). Qed.
Lemma lem5094291 {B : Type'} (x : B) (y : B) (z : B) : term251 B x y z.
Proof. exact (@lem5094290 B x y z). Qed.
Lemma lem5094292 {A B : Type'} (f : A -> B) (g : B -> A) (x : B) : term253 A B f g x.
Proof. exact (@lem5094291 B (term45 A B f g x) x (term45 A B f g x)). Qed.
Lemma lem5094295 {A B : Type'} (x : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term194 A B t x f s) (h2 : term69 A B n s t g f) : x = (term45 A B f g x).
Proof. exact (@lem5094292 A B f g x (@lem5094288 A B x n s t g f h1 h2)). Qed.
Lemma lem5094296 {A B : Type'} (x : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term194 A B t x f s) (h2 : term69 A B n s t g f) : term254 A B f g x.
Proof. exact (fun h0 : term255 A B f g x => @lem5094295 A B x n s t g f h1 h2). Qed.
Lemma lem5094298 (p : Prop) : (term217 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5094299 {A B : Type'} (f : A -> B) (g : B -> A) (x : B) : (term254 A B f g x) = (x = (term45 A B f g x)).
Proof. exact (@lem5094298 (x = (term45 A B f g x))). Qed.
Lemma lem5094300 {A B : Type'} (x : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term194 A B t x f s) (h2 : term69 A B n s t g f) : x = (term45 A B f g x).
Proof. exact (EQ_MP (@lem5094299 A B f g x) (@lem5094296 A B x n s t g f h1 h2)). Qed.
Lemma lem5094302 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term194 A B t x f s) : t x.
Proof. exact (proj1 (@lem5093692 A B t x f s h1)). Qed.
Lemma lem5094303 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term194 A B t x f s) : term216 B t x.
Proof. exact (fun h0 : term148 B t x => @lem5094302 A B t x f s h1). Qed.
Lemma lem5094305 (p : Prop) : (term217 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5094306 {B : Type'} (t : B -> Prop) (x : B) : (term216 B t x) = (t x).
Proof. exact (@lem5094305 (t x)). Qed.
Lemma lem5094307 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term194 A B t x f s) : t x.
Proof. exact (EQ_MP (@lem5094306 B t x) (@lem5094303 A B t x f s h1)). Qed.
Lemma lem5094313 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5094314 {A B : Type'} (s : A -> Prop) (g : B -> A) (t : B -> Prop) (_66240 : B) : (term206 A B t s g _66240) = (term256 A B s g t _66240).
Proof. exact (@lem5094313 (term179 A B s g _66240) (term148 B t _66240)). Qed.
Lemma lem5094320 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5094321 {A B : Type'} (s : A -> Prop) (g : B -> A) (t : B -> Prop) (_66240 : B) : (term257 A B t s g _66240) = (term258 A B s g t _66240).
Proof. exact (MK_COMB (@lem5094320) (@lem5094314 A B s g t _66240)). Qed.
Lemma lem5094327 {A B : Type'} (s : A -> Prop) (g : B -> A) (t : B -> Prop) (_66240 : B) : (term256 A B s g t _66240) = (term256 A B s g t _66240).
Proof. exact (eq_refl (term256 A B s g t _66240)). Qed.
Lemma lem5094328 {A B : Type'} (s : A -> Prop) (g : B -> A) (t : B -> Prop) (_66240 : B) : ((term206 A B t s g _66240) = (term256 A B s g t _66240)) = ((term256 A B s g t _66240) = (term256 A B s g t _66240)).
Proof. exact (MK_COMB (@lem5094321 A B s g t _66240) (@lem5094327 A B s g t _66240)). Qed.
Lemma lem5094330 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5094331 (x : Prop) : (x = x) = True.
Proof. exact (@lem5094330 Prop x). Qed.
Lemma lem5094332 {A B : Type'} (s : A -> Prop) (g : B -> A) (t : B -> Prop) (_66240 : B) : ((term256 A B s g t _66240) = (term256 A B s g t _66240)) = True.
Proof. exact (@lem5094331 (term256 A B s g t _66240)). Qed.
Lemma lem5094333 {A B : Type'} (s : A -> Prop) (g : B -> A) (t : B -> Prop) (_66240 : B) : ((term206 A B t s g _66240) = (term256 A B s g t _66240)) = True.
Proof. exact (TRANS (@lem5094328 A B s g t _66240) (@lem5094332 A B s g t _66240)). Qed.
Lemma lem5094334 {A B : Type'} (s : A -> Prop) (g : B -> A) (t : B -> Prop) (_66240 : B) : True = ((term206 A B t s g _66240) = (term256 A B s g t _66240)).
Proof. exact (SYM (@lem5094333 A B s g t _66240)). Qed.
Lemma lem5094335 {A B : Type'} (s : A -> Prop) (g : B -> A) (t : B -> Prop) (_66240 : B) : (term206 A B t s g _66240) = (term256 A B s g t _66240).
Proof. exact (EQ_MP (@lem5094334 A B s g t _66240) (@lem0)). Qed.
Lemma lem5094336 {A B : Type'} (_66240 : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term256 A B s g t _66240.
Proof. exact (EQ_MP (@lem5094335 A B s g t _66240) (@lem5093879 A B _66240 n s t g f h1)). Qed.
Lemma lem5094338 (b : Prop) (a : Prop) : (a \/ b) = (term221 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5094339 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> A) (_66240 : B) : (term256 A B s g t _66240) = (term259 A B t s g _66240).
Proof. exact (@lem5094338 (term148 B t _66240) (term179 A B s g _66240)). Qed.
Lemma lem5094341 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5094342 {B : Type'} (t : B -> Prop) (_66240 : B) : (term223 B t _66240) = (t _66240).
Proof. exact (@lem5094341 (t _66240)). Qed.
Lemma lem5094343 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5094344 {B : Type'} (t : B -> Prop) (_66240 : B) : (term224 B t _66240) = (term40 B t _66240).
Proof. exact (MK_COMB (@lem5094343) (@lem5094342 B t _66240)). Qed.
Lemma lem5094345 {A B : Type'} (s : A -> Prop) (g : B -> A) (_66240 : B) : (term179 A B s g _66240) = (term179 A B s g _66240).
Proof. exact (eq_refl (term179 A B s g _66240)). Qed.
Lemma lem5094346 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> A) (_66240 : B) : (term259 A B t s g _66240) = (term260 A B t s g _66240).
Proof. exact (MK_COMB (@lem5094344 B t _66240) (@lem5094345 A B s g _66240)). Qed.
Lemma lem5094347 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> A) (_66240 : B) : (term256 A B s g t _66240) = (term260 A B t s g _66240).
Proof. exact (TRANS (@lem5094339 A B t s g _66240) (@lem5094346 A B t s g _66240)). Qed.
Lemma lem5094350 {A B : Type'} (_66240 : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term260 A B t s g _66240.
Proof. exact (EQ_MP (@lem5094347 A B t s g _66240) (@lem5094336 A B _66240 n s t g f h1)). Qed.
Lemma lem5094351 {A B : Type'} (_66240 : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term260 A B t s g _66240.
Proof. exact (@lem5094350 A B _66240 n s t g f h1). Qed.
Lemma lem5094352 {A B : Type'} (x : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term260 A B t s g x.
Proof. exact (@lem5094351 A B x n s t g f h1). Qed.
Lemma lem5094355 {A B : Type'} (x : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term194 A B t x f s) (h2 : term69 A B n s t g f) : term179 A B s g x.
Proof. exact (@lem5094352 A B x n s t g f h2 (@lem5094307 A B t x f s h1)). Qed.
Lemma lem5094356 {A B : Type'} (x : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term194 A B t x f s) (h2 : term69 A B n s t g f) : term261 A B s g x.
Proof. exact (fun h0 : term262 A B s g x => @lem5094355 A B x n s t g f h1 h2). Qed.
Lemma lem5094358 (p : Prop) : (term217 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5094359 {A B : Type'} (s : A -> Prop) (g : B -> A) (x : B) : (term261 A B s g x) = (term179 A B s g x).
Proof. exact (@lem5094358 (term179 A B s g x)). Qed.
Lemma lem5094360 {A B : Type'} (x : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term194 A B t x f s) (h2 : term69 A B n s t g f) : term179 A B s g x.
Proof. exact (EQ_MP (@lem5094359 A B s g x) (@lem5094356 A B x n s t g f h1 h2)). Qed.
Lemma lem5094362 (a : Prop) (b : Prop) : (term263 a b) = (term264 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5094363 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_66242 : A) : (term191 A B x f s _66242) = (term265 A B x f s _66242).
Proof. exact (@lem5094362 (x = (f _66242)) (@I (A -> Prop) s _66242)). Qed.
Lemma lem5094365 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5094366 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_66242 : A) : (term265 A B x f s _66242) = (term266 A B x f s _66242).
Proof. exact (@lem5094365 (term188 A B x f s _66242)). Qed.
Lemma lem5094367 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_66242 : A) : (term191 A B x f s _66242) = (term266 A B x f s _66242).
Proof. exact (TRANS (@lem5094363 A B x f s _66242) (@lem5094366 A B x f s _66242)). Qed.
Lemma lem5094369 {A B : Type'} (x : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term194 A B t x f s) (h2 : term69 A B n s t g f) : term267 A B f s g x.
Proof. exact (conj (@lem5094300 A B x n s t g f h1 h2) (@lem5094360 A B x n s t g f h1 h2)). Qed.
Lemma lem5094371 {A B : Type'} (_66242 : A) (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term194 A B t x f s) : term266 A B x f s _66242.
Proof. exact (EQ_MP (@lem5094367 A B x f s _66242) (@lem5093861 A B _66242 t x f s h1)). Qed.
Lemma lem5094372 {A B : Type'} (_66242 : A) (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term194 A B t x f s) : term266 A B x f s _66242.
Proof. exact (@lem5094371 A B _66242 t x f s h1). Qed.
Lemma lem5094373 {A B : Type'} (g : B -> A) (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term194 A B t x f s) : term268 A B f s g x.
Proof. exact (@lem5094372 A B (g x) t x f s h1). Qed.
Lemma lem5094376 {A B : Type'} (x : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term194 A B t x f s) (h2 : term69 A B n s t g f) : False.
Proof. exact (@lem5094373 A B g t x f s h1 (@lem5094369 A B x n s t g f h1 h2)). Qed.
Lemma lem5094377 {A B : Type'} (x : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term194 A B t x f s) (h2 : term69 A B n s t g f) : term269.
Proof. exact (fun h0 : ~ False => @lem5094376 A B x n s t g f h1 h2). Qed.
Lemma lem5094379 (p : Prop) : (term217 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5094380 : term269 = False.
Proof. exact (@lem5094379 False). Qed.
Lemma lem5094381 {A B : Type'} (x : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term194 A B t x f s) (h2 : term69 A B n s t g f) : False.
Proof. exact (EQ_MP (@lem5094380) (@lem5094377 A B x n s t g f h1 h2)). Qed.
Lemma lem5094457 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term189 A B t x f s x') : @I (A -> Prop) s x'.
Proof. exact (proj2 (@lem5093696 A B t x f s x' h1)). Qed.
Lemma lem5094458 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term189 A B t x f s x') : term270 A s x'.
Proof. exact (fun h0 : term173 A s x' => @lem5094457 A B t x f s x' h1). Qed.
Lemma lem5094460 (p : Prop) : (term217 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5094461 {A : Type'} (s : A -> Prop) (x' : A) : (term270 A s x') = (@I (A -> Prop) s x').
Proof. exact (@lem5094460 (@I (A -> Prop) s x')). Qed.
Lemma lem5094462 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term189 A B t x f s x') : @I (A -> Prop) s x'.
Proof. exact (EQ_MP (@lem5094461 A s x') (@lem5094458 A B t x f s x' h1)). Qed.
Lemma lem5094468 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5094469 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (_66244 : A) : (term214 A B s t f _66244) = (term271 A B t f s _66244).
Proof. exact (@lem5094468 (term56 A B t f _66244) (term173 A s _66244)). Qed.
Lemma lem5094475 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5094476 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (_66244 : A) : (term272 A B s t f _66244) = (term273 A B t f s _66244).
Proof. exact (MK_COMB (@lem5094475) (@lem5094469 A B t f s _66244)). Qed.
Lemma lem5094482 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (_66244 : A) : (term271 A B t f s _66244) = (term271 A B t f s _66244).
Proof. exact (eq_refl (term271 A B t f s _66244)). Qed.
Lemma lem5094483 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (_66244 : A) : ((term214 A B s t f _66244) = (term271 A B t f s _66244)) = ((term271 A B t f s _66244) = (term271 A B t f s _66244)).
Proof. exact (MK_COMB (@lem5094476 A B t f s _66244) (@lem5094482 A B t f s _66244)). Qed.
Lemma lem5094485 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5094486 (x : Prop) : (x = x) = True.
Proof. exact (@lem5094485 Prop x). Qed.
Lemma lem5094487 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (_66244 : A) : ((term271 A B t f s _66244) = (term271 A B t f s _66244)) = True.
Proof. exact (@lem5094486 (term271 A B t f s _66244)). Qed.
Lemma lem5094488 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (_66244 : A) : ((term214 A B s t f _66244) = (term271 A B t f s _66244)) = True.
Proof. exact (TRANS (@lem5094483 A B t f s _66244) (@lem5094487 A B t f s _66244)). Qed.
Lemma lem5094489 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (_66244 : A) : True = ((term214 A B s t f _66244) = (term271 A B t f s _66244)).
Proof. exact (SYM (@lem5094488 A B t f s _66244)). Qed.
Lemma lem5094490 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (_66244 : A) : (term214 A B s t f _66244) = (term271 A B t f s _66244).
Proof. exact (EQ_MP (@lem5094489 A B t f s _66244) (@lem0)). Qed.
Lemma lem5094491 {A B : Type'} (_66244 : A) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term271 A B t f s _66244.
Proof. exact (EQ_MP (@lem5094490 A B t f s _66244) (@lem5093986 A B _66244 n s t g f h1)). Qed.
Lemma lem5094493 (b : Prop) (a : Prop) : (a \/ b) = (term221 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5094494 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_66244 : A) : (term271 A B t f s _66244) = (term274 A B s t f _66244).
Proof. exact (@lem5094493 (term173 A s _66244) (term56 A B t f _66244)). Qed.
Lemma lem5094496 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5094497 {A : Type'} (s : A -> Prop) (_66244 : A) : (term275 A s _66244) = (@I (A -> Prop) s _66244).
Proof. exact (@lem5094496 (@I (A -> Prop) s _66244)). Qed.
Lemma lem5094498 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5094499 {A : Type'} (s : A -> Prop) (_66244 : A) : (term276 A s _66244) = (term277 A s _66244).
Proof. exact (MK_COMB (@lem5094498) (@lem5094497 A s _66244)). Qed.
Lemma lem5094500 {A B : Type'} (t : B -> Prop) (f : A -> B) (_66244 : A) : (term56 A B t f _66244) = (term56 A B t f _66244).
Proof. exact (eq_refl (term56 A B t f _66244)). Qed.
Lemma lem5094501 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_66244 : A) : (term274 A B s t f _66244) = (term278 A B s t f _66244).
Proof. exact (MK_COMB (@lem5094499 A s _66244) (@lem5094500 A B t f _66244)). Qed.
Lemma lem5094502 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_66244 : A) : (term271 A B t f s _66244) = (term278 A B s t f _66244).
Proof. exact (TRANS (@lem5094494 A B s t f _66244) (@lem5094501 A B s t f _66244)). Qed.
Lemma lem5094505 {A B : Type'} (_66244 : A) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term278 A B s t f _66244.
Proof. exact (EQ_MP (@lem5094502 A B s t f _66244) (@lem5094491 A B _66244 n s t g f h1)). Qed.
Lemma lem5094506 {A B : Type'} (_66244 : A) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term278 A B s t f _66244.
Proof. exact (@lem5094505 A B _66244 n s t g f h1). Qed.
Lemma lem5094507 {A B : Type'} (x' : A) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term278 A B s t f x'.
Proof. exact (@lem5094506 A B x' n s t g f h1). Qed.
Lemma lem5094510 {A B : Type'} (x : B) (x' : A) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term189 A B t x f s x') (h2 : term69 A B n s t g f) : term56 A B t f x'.
Proof. exact (@lem5094507 A B x' n s t g f h2 (@lem5094462 A B t x f s x' h1)). Qed.
Lemma lem5094511 {A B : Type'} (x : B) (x' : A) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term189 A B t x f s x') (h2 : term69 A B n s t g f) : term279 A B t f x'.
Proof. exact (fun h0 : term211 A B t f x' => @lem5094510 A B x x' n s t g f h1 h2). Qed.
Lemma lem5094513 (p : Prop) : (term217 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5094514 {A B : Type'} (t : B -> Prop) (f : A -> B) (x' : A) : (term279 A B t f x') = (term56 A B t f x').
Proof. exact (@lem5094513 (term56 A B t f x')). Qed.
Lemma lem5094515 {A B : Type'} (x : B) (x' : A) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term189 A B t x f s x') (h2 : term69 A B n s t g f) : term56 A B t f x'.
Proof. exact (EQ_MP (@lem5094514 A B t f x') (@lem5094511 A B x x' n s t g f h1 h2)). Qed.
Lemma lem5094518 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5094520 {A B : Type'} (t : B -> Prop) (f : A -> B) (x' : A) : (term211 A B t f x') = (term280 A B t f x').
Proof. exact (@lem5094518 (term56 A B t f x')). Qed.
Lemma lem5094523 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term189 A B t x f s x') : term280 A B t f x'.
Proof. exact (EQ_MP (@lem5094520 A B t f x') (@lem5093958 A B t x f s x' h1)). Qed.
Lemma lem5094526 {A B : Type'} (x : B) (x' : A) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term189 A B t x f s x') (h2 : term69 A B n s t g f) : False.
Proof. exact (@lem5094523 A B t x f s x' h1 (@lem5094515 A B x x' n s t g f h1 h2)). Qed.
Lemma lem5094527 {A B : Type'} (x : B) (x' : A) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term189 A B t x f s x') (h2 : term69 A B n s t g f) : term269.
Proof. exact (fun h0 : ~ False => @lem5094526 A B x x' n s t g f h1 h2). Qed.
Lemma lem5094529 (p : Prop) : (term217 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5094530 : term269 = False.
Proof. exact (@lem5094529 False). Qed.
Lemma lem5094532 {A B : Type'} (x : B) (x' : A) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term189 A B t x f s x') (h2 : term69 A B n s t g f) : False.
Proof. exact (EQ_MP (@lem5094530) (@lem5094527 A B x x' n s t g f h1 h2)). Qed.
Lemma lem5094533 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term69 A B n s t g f) (h2 : term169 A B t x f s x') : False.
Proof. exact (or_elim (@lem5093687 A B t x f s x' h2) (fun h0 : term194 A B t x f s => @lem5094381 A B x n s t g f h0 h1) (fun h0 : term189 A B t x f s x' => @lem5094532 A B x x' n s t g f h0 h1)). Qed.
Lemma lem5094534 {A B : Type'} (x : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term114 A B t x f s) (h2 : term69 A B n s t g f) : False.
Proof. exact (ex_elim (@lem5093547 A B t x f s h1) (fun x' : A => fun h0 : term171 A B t x f s x' => @lem5094533 A B n g t x f s x' h2 h0)). Qed.
Lemma lem5094535 {A B : Type'} (x : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term114 A B t x f s) (h2 : term69 A B n s t g f) : (term114 A B t x f s) = False.
Proof. exact (prop_ext (fun h3 : term114 A B t x f s => @lem5094534 A B x n s t g f h1 h2) (fun h3 : False => @lem5093246 A B t x f s h1)). Qed.
Lemma lem5094536 {A B : Type'} (x : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term114 A B t x f s) (h2 : term69 A B n s t g f) : False.
Proof. exact (EQ_MP (@lem5094535 A B x n s t g f h1 h2) (@lem5093246 A B t x f s h1)). Qed.
Lemma lem5094537 {A B : Type'} (x : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term113 A B t x f s.
Proof. exact (fun h0 : term114 A B t x f s => @lem5094536 A B x n s t g f h0 h1). Qed.
Lemma lem5094538 {A B : Type'} (x : B) (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : (t x) = (term80 A B x f s).
Proof. exact (EQ_MP (@lem5093245 A B t x f s) (@lem5094537 A B x n s t g f h1)). Qed.
Lemma lem5094543 {A B : Type'} (n : nat) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term69 A B n s t g f) : term83 A B t f s.
Proof. exact (fun x : B => @lem5094538 A B x n s t g f h1). Qed.
Lemma lem5094544 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term84 A B n g t f s.
Proof. exact (fun h0 : term69 A B n s t g f => @lem5094543 A B n s t g f h0). Qed.
Lemma lem5094549 {A B : Type'} (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term96 A B g t f s.
Proof. exact (fun n : nat => @lem5094544 A B n g t f s). Qed.
Lemma lem5094554 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term100 A B t f s.
Proof. exact (fun g : B -> A => @lem5094549 A B g t f s). Qed.
Lemma lem5094559 {A B : Type'} (f : A -> B) (s : A -> Prop) : term104 A B f s.
Proof. exact (fun t : B -> Prop => @lem5094554 A B t f s). Qed.
Lemma lem5094564 {A B : Type'} (s : A -> Prop) : term108 A B s.
Proof. exact (fun f : A -> B => @lem5094559 A B f s). Qed.
Lemma lem5094569 {A B : Type'} : term112 A B.
Proof. exact (fun s : A -> Prop => @lem5094564 A B s). Qed.
Lemma lem5094570 {A B : Type'} : term111 A B.
Proof. exact (EQ_MP (@lem5093240 A B) (@lem5094569 A B)). Qed.
Lemma lem5094571 {A B : Type'} (s : A -> Prop) : term281 A B s.
Proof. exact (@lem5094570 A B s). Qed.
Lemma lem5094572 {A B : Type'} (s : A -> Prop) : (term281 A B s) = (term107 A B s).
Proof. exact (eq_refl (term281 A B s)). Qed.
Lemma lem5094573 {A B : Type'} (s : A -> Prop) : term107 A B s.
Proof. exact (EQ_MP (@lem5094572 A B s) (@lem5094571 A B s)). Qed.
Lemma lem5094574 {A B : Type'} (s : A -> Prop) (f : A -> B) : term282 A B s f.
Proof. exact (@lem5094573 A B s f). Qed.
Lemma lem5094575 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term282 A B s f) = (term103 A B f s).
Proof. exact (eq_refl (term282 A B s f)). Qed.
Lemma lem5094576 {A B : Type'} (f : A -> B) (s : A -> Prop) : term103 A B f s.
Proof. exact (EQ_MP (@lem5094575 A B f s) (@lem5094574 A B s f)). Qed.
Lemma lem5094577 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : term283 A B f s t.
Proof. exact (@lem5094576 A B f s t). Qed.
Lemma lem5094578 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term283 A B f s t) = (term99 A B t f s).
Proof. exact (eq_refl (term283 A B f s t)). Qed.
Lemma lem5094579 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term99 A B t f s.
Proof. exact (EQ_MP (@lem5094578 A B t f s) (@lem5094577 A B f s t)). Qed.
Lemma lem5094580 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (g : B -> A) : term284 A B t f s g.
Proof. exact (@lem5094579 A B t f s g). Qed.
Lemma lem5094581 {A B : Type'} (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term284 A B t f s g) = (term95 A B g t f s).
Proof. exact (eq_refl (term284 A B t f s g)). Qed.
Lemma lem5094582 {A B : Type'} (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term95 A B g t f s.
Proof. exact (EQ_MP (@lem5094581 A B g t f s) (@lem5094580 A B t f s g)). Qed.
Lemma lem5094583 {A B : Type'} (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (n : nat) : term285 A B g t f s n.
Proof. exact (@lem5094582 A B g t f s n). Qed.
Lemma lem5094584 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term285 A B g t f s n) = (term86 A B n g t f s).
Proof. exact (eq_refl (term285 A B g t f s n)). Qed.
Lemma lem5094585 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term86 A B n g t f s.
Proof. exact (EQ_MP (@lem5094584 A B n g t f s) (@lem5094583 A B g t f s n)). Qed.
Lemma lem5094587 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term86 A B n g t f s.
Proof. exact (@lem5092976 A B n g t f s (@lem5094585 A B n g t f s)). Qed.
Lemma lem5094588 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term87 A B n g t f s) : False.
Proof. exact (@lem5094587 A B n g t f s (@lem5092960 A B n g t f s h1)). Qed.
Lemma lem5094589 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term87 A B n g t f s) : (term87 A B n g t f s) = False.
Proof. exact (prop_ext (fun h2 : term87 A B n g t f s => @lem5094588 A B n g t f s h1) (fun h2 : False => @lem5092960 A B n g t f s h1)). Qed.
Lemma lem5094590 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term87 A B n g t f s) : False.
Proof. exact (EQ_MP (@lem5094589 A B n g t f s h1) (@lem5092960 A B n g t f s h1)). Qed.
Lemma lem5094591 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term86 A B n g t f s.
Proof. exact (fun h0 : term87 A B n g t f s => @lem5094590 A B n g t f s h0). Qed.
Lemma lem5094592 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term84 A B n g t f s.
Proof. exact (EQ_MP (@lem5092959 A B n g t f s) (@lem5094591 A B n g t f s)). Qed.
Lemma lem5094593 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term38 A B n g t f s.
Proof. exact (EQ_MP (@lem5092955 A B n g t f s) (@lem5094592 A B n g t f s)). Qed.
Lemma lem5094594 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term37 A B n g t f s.
Proof. exact (EQ_MP (@lem5092812 A B n g t f s) (@lem5094593 A B n g t f s)). Qed.
Lemma lem5094595 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (s : A -> Prop) (n : nat) (h1 : term13 A B s t g f) (h2 : term14 A B t s f g) (h3 : @HAS_SIZE A s n) : t = (@IMAGE A B f s).
Proof. exact (@lem5094594 A B n g t f s (@lem5092763 A B t f g s n h1 h2 h3)). Qed.
Lemma lem5094597 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : term6 A B f s n.
Proof. exact (EQ_MP (@lem5092691 A B f s n) (@lem5092690 A B f s n)). Qed.
Lemma lem5094598 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : term6 A B f s n.
Proof. exact (@lem5094597 A B f s n). Qed.
Lemma lem5094600 (p : Prop) : p = (term85 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5094601 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term7 A B f s n) = (term286 A B f s n).
Proof. exact (@lem5094600 (term7 A B f s n)). Qed.
Lemma lem5094602 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term286 A B f s n) = (term7 A B f s n).
Proof. exact (SYM (@lem5094601 A B f s n)). Qed.
Lemma lem5094603 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term287 A B f s n) : term287 A B f s n.
Proof. exact (h1). Qed.
Lemma lem5094606 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term288 A B g f s n) : term288 A B g f s n.
Proof. exact (h1). Qed.
Lemma lem5094607 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (n : nat) : term289 A B g f s n.
Proof. exact (fun h0 : term288 A B g f s n => @lem5094606 A B g f s n h0). Qed.
Lemma lem5094608 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term289 A B g f s n) : term289 A B g f s n.
Proof. exact (h1). Qed.
Lemma lem5094609 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term288 A B g f s n) : term288 A B g f s n.
Proof. exact (h1). Qed.
Lemma lem5094610 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term288 A B g f s n) (h2 : term289 A B g f s n) : term288 A B g f s n.
Proof. exact (@lem5094608 A B g f s n h2 (@lem5094609 A B g f s n h1)). Qed.
Lemma lem5094611 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term288 A B g f s n) : term290 A B g f s n.
Proof. exact (fun h0 : term289 A B g f s n => @lem5094610 A B g f s n h1 h0). Qed.
Lemma lem5094612 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term289 A B g f s n) : term289 A B g f s n.
Proof. exact (h1). Qed.
Lemma lem5094613 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term288 A B g f s n) (h2 : term289 A B g f s n) : term288 A B g f s n.
Proof. exact (@lem5094611 A B g f s n h1 (@lem5094612 A B g f s n h2)). Qed.
Lemma lem5094614 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term289 A B g f s n) : term289 A B g f s n.
Proof. exact (fun h0 : term288 A B g f s n => @lem5094613 A B g f s n h0 h1). Qed.
Lemma lem5094615 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (n : nat) : term291 A B g f s n.
Proof. exact (fun h0 : term289 A B g f s n => @lem5094614 A B g f s n h0). Qed.
Lemma lem5094618 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (n : nat) : term289 A B g f s n.
Proof. exact (@lem5094615 A B g f s n (@lem5094607 A B g f s n)). Qed.
Lemma lem5094619 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (n : nat) : term289 A B g f s n.
Proof. exact (@lem5094618 A B g f s n). Qed.
Lemma lem5094659 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5094660 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term286 A B f s n) = (term292 A B f s n).
Proof. exact (@lem5094659 (term287 A B f s n)). Qed.
Lemma lem5094662 (t : Prop) : (term92 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5094663 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term292 A B f s n) = (term7 A B f s n).
Proof. exact (@lem5094662 (term7 A B f s n)). Qed.
Lemma lem5094666 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term286 A B f s n) = (term7 A B f s n).
Proof. exact (TRANS (@lem5094660 A B f s n) (@lem5094663 A B f s n)). Qed.
Lemma lem5094681 {A : Type'} (s : A -> Prop) (n : nat) : (term293 A s n) = (term293 A s n).
Proof. exact (eq_refl (term293 A s n)). Qed.
Lemma lem5094682 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term294 A B f s n) = (term295 A B f s n).
Proof. exact (MK_COMB (@lem5094681 A s n) (@lem5094666 A B f s n)). Qed.
Lemma lem5094685 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term296 A B s f g) = (term296 A B s f g).
Proof. exact (eq_refl (term296 A B s f g)). Qed.
Lemma lem5094686 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (n : nat) : (term297 A B g f s n) = (term298 A B g f s n).
Proof. exact (MK_COMB (@lem5094685 A B s f g) (@lem5094682 A B f s n)). Qed.
Lemma lem5094689 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term299 A B s g f) = (term299 A B s g f).
Proof. exact (eq_refl (term299 A B s g f)). Qed.
Lemma lem5094690 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (n : nat) : (term288 A B g f s n) = (term300 A B g f s n).
Proof. exact (MK_COMB (@lem5094689 A B s g f) (@lem5094686 A B g f s n)). Qed.
Lemma lem5094693 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term301 A B f s n) = (term302 A B f s n).
Proof. exact (fun_ext (fun g : B -> A => @lem5094690 A B g f s n)). Qed.
Lemma lem5094694 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem5094695 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term303 A B f s n) = (term304 A B f s n).
Proof. exact (MK_COMB (@lem5094694 A B) (@lem5094693 A B f s n)). Qed.
Lemma lem5094700 {A B : Type'} (s : A -> Prop) (n : nat) : (term305 A B s n) = (term306 A B s n).
Proof. exact (fun_ext (fun f : A -> B => @lem5094695 A B f s n)). Qed.
Lemma lem5094701 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5094702 {A B : Type'} (s : A -> Prop) (n : nat) : (term307 A B s n) = (term308 A B s n).
Proof. exact (MK_COMB (@lem5094701 A B) (@lem5094700 A B s n)). Qed.
Lemma lem5094707 {A B : Type'} (n : nat) : (term309 A B n) = (term310 A B n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5094702 A B s n)). Qed.
Lemma lem5094708 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5094709 {A B : Type'} (n : nat) : (term311 A B n) = (term312 A B n).
Proof. exact (MK_COMB (@lem5094708 A) (@lem5094707 A B n)). Qed.
Lemma lem5094714 {A B : Type'} : (term313 A B) = (term314 A B).
Proof. exact (fun_ext (fun n : nat => @lem5094709 A B n)). Qed.
Lemma lem5094715 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5094724 {A B : Type'} : (term315 A B) = (term316 A B).
Proof. exact (MK_COMB (@lem5094715) (@lem5094714 A B)). Qed.
Lemma lem5094725 {A : Type'} (s : A -> Prop) (n : nat) : (@HAS_SIZE A s n) = (@HAS_SIZE A s n).
Proof. exact (eq_refl (@HAS_SIZE A s n)). Qed.
Lemma lem5094738 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term317 A B s f x y) = (term317 A B s f x y).
Proof. exact (eq_refl (term317 A B s f x y)). Qed.
Lemma lem5094739 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term318 A B s f x) = (term318 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem5094738 A B s f x y)). Qed.
Lemma lem5094740 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5094741 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term319 A B s f x) = (term319 A B s f x).
Proof. exact (MK_COMB (@lem5094740 A) (@lem5094739 A B s f x)). Qed.
Lemma lem5094742 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term320 A B s f) = (term320 A B s f).
Proof. exact (fun_ext (fun x : A => @lem5094741 A B s f x)). Qed.
Lemma lem5094743 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5094744 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term321 A B s f) = (term321 A B s f).
Proof. exact (MK_COMB (@lem5094743 A) (@lem5094742 A B s f)). Qed.
Lemma lem5094745 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5094746 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term322 A B s f) = (term322 A B s f).
Proof. exact (MK_COMB (@lem5094745) (@lem5094744 A B s f)). Qed.
Lemma lem5094747 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term7 A B f s n) = (term7 A B f s n).
Proof. exact (MK_COMB (@lem5094746 A B s f) (@lem5094725 A s n)). Qed.
Lemma lem5094750 {A : Type'} (s : A -> Prop) (n : nat) : (term293 A s n) = (term293 A s n).
Proof. exact (eq_refl (term293 A s n)). Qed.
Lemma lem5094751 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term295 A B f s n) = (term295 A B f s n).
Proof. exact (MK_COMB (@lem5094750 A s n) (@lem5094747 A B f s n)). Qed.
Lemma lem5094760 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term323 A B s f g y) = (term323 A B s f g y).
Proof. exact (eq_refl (term323 A B s f g y)). Qed.
Lemma lem5094761 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term324 A B s f g) = (term324 A B s f g).
Proof. exact (fun_ext (fun y : B => @lem5094760 A B s f g y)). Qed.
Lemma lem5094762 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5094763 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term29 A B s f g) = (term29 A B s f g).
Proof. exact (MK_COMB (@lem5094762 B) (@lem5094761 A B s f g)). Qed.
Lemma lem5094764 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5094765 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term296 A B s f g) = (term296 A B s f g).
Proof. exact (MK_COMB (@lem5094764) (@lem5094763 A B s f g)). Qed.
Lemma lem5094766 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (n : nat) : (term298 A B g f s n) = (term298 A B g f s n).
Proof. exact (MK_COMB (@lem5094765 A B s f g) (@lem5094751 A B f s n)). Qed.
Lemma lem5094775 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term325 A B s g f x) = (term325 A B s g f x).
Proof. exact (eq_refl (term325 A B s g f x)). Qed.
Lemma lem5094776 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term326 A B s g f) = (term326 A B s g f).
Proof. exact (fun_ext (fun x : A => @lem5094775 A B s g f x)). Qed.
Lemma lem5094777 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5094778 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term23 A B s g f) = (term23 A B s g f).
Proof. exact (MK_COMB (@lem5094777 A) (@lem5094776 A B s g f)). Qed.
Lemma lem5094779 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5094780 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term299 A B s g f) = (term299 A B s g f).
Proof. exact (MK_COMB (@lem5094779) (@lem5094778 A B s g f)). Qed.
Lemma lem5094781 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (n : nat) : (term300 A B g f s n) = (term300 A B g f s n).
Proof. exact (MK_COMB (@lem5094780 A B s g f) (@lem5094766 A B g f s n)). Qed.
Lemma lem5094782 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term302 A B f s n) = (term302 A B f s n).
Proof. exact (fun_ext (fun g : B -> A => @lem5094781 A B g f s n)). Qed.
Lemma lem5094783 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem5094784 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term304 A B f s n) = (term304 A B f s n).
Proof. exact (MK_COMB (@lem5094783 A B) (@lem5094782 A B f s n)). Qed.
Lemma lem5094785 {A B : Type'} (s : A -> Prop) (n : nat) : (term306 A B s n) = (term306 A B s n).
Proof. exact (fun_ext (fun f : A -> B => @lem5094784 A B f s n)). Qed.
Lemma lem5094786 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5094787 {A B : Type'} (s : A -> Prop) (n : nat) : (term308 A B s n) = (term308 A B s n).
Proof. exact (MK_COMB (@lem5094786 A B) (@lem5094785 A B s n)). Qed.
Lemma lem5094788 {A B : Type'} (n : nat) : (term310 A B n) = (term310 A B n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5094787 A B s n)). Qed.
Lemma lem5094789 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5094790 {A B : Type'} (n : nat) : (term312 A B n) = (term312 A B n).
Proof. exact (MK_COMB (@lem5094789 A) (@lem5094788 A B n)). Qed.
Lemma lem5094791 {A B : Type'} : (term314 A B) = (term314 A B).
Proof. exact (fun_ext (fun n : nat => @lem5094790 A B n)). Qed.
Lemma lem5094792 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5094793 {A B : Type'} : (term316 A B) = (term316 A B).
Proof. exact (MK_COMB (@lem5094792) (@lem5094791 A B)). Qed.
Lemma lem5094866 {A B : Type'} : (term315 A B) = (term316 A B).
Proof. exact (TRANS (@lem5094724 A B) (@lem5094793 A B)). Qed.
Lemma lem5094867 {A B : Type'} : (term316 A B) = (term315 A B).
Proof. exact (SYM (@lem5094866 A B)). Qed.
Lemma lem5094868 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term23 A B s g f) : term23 A B s g f.
Proof. exact (h1). Qed.
Lemma lem5094872 (p : Prop) : p = (term85 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5094873 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term7 A B f s n) = (term286 A B f s n).
Proof. exact (@lem5094872 (term7 A B f s n)). Qed.
Lemma lem5094874 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term286 A B f s n) = (term7 A B f s n).
Proof. exact (SYM (@lem5094873 A B f s n)). Qed.
Lemma lem5094875 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term287 A B f s n) : term287 A B f s n.
Proof. exact (h1). Qed.
Lemma lem5094886 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term325 A B s g f x) = (term327 A B s g f x).
Proof. exact (@lem17265 (@IN A x s) (term328 A B s g f x)). Qed.
Lemma lem5094887 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term326 A B s g f) = (term329 A B s g f).
Proof. exact (fun_ext (fun x : A => @lem5094886 A B s g f x)). Qed.
Lemma lem5094888 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5094941 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term23 A B s g f) = (term330 A B s g f).
Proof. exact (MK_COMB (@lem5094888 A) (@lem5094887 A B s g f)). Qed.
Lemma lem5094942 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term23 A B s g f) : term330 A B s g f.
Proof. exact (EQ_MP (@lem5094941 A B s g f) (@lem5094868 A B s g f h1)). Qed.
Lemma lem5095015 {A : Type'} (s : A -> Prop) (n : nat) (h1 : @HAS_SIZE A s n) : @HAS_SIZE A s n.
Proof. exact (h1). Qed.
Lemma lem5095030 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term331 A B s f x y) = (term332 A B s f x y).
Proof. exact (@lem17362 (term333 A B s x f y) (x = y)). Qed.
Lemma lem5095031 {A : Type'} (P : A -> Prop) : (term334 A P) = (term335 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5095032 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term336 A B s f x) = (term337 A B s f x).
Proof. exact (@lem5095031 A (term318 A B s f x)). Qed.
Lemma lem5095033 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term338 A B s f x y) = (term317 A B s f x y).
Proof. exact (eq_refl (term338 A B s f x y)). Qed.
Lemma lem5095034 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5095035 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term339 A B s f x y) = (term331 A B s f x y).
Proof. exact (MK_COMB (@lem5095034) (@lem5095033 A B s f x y)). Qed.
Lemma lem5095036 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term339 A B s f x y) = (term332 A B s f x y).
Proof. exact (TRANS (@lem5095035 A B s f x y) (@lem5095030 A B s f x y)). Qed.
Lemma lem5095037 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term340 A B s f x) = (term341 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem5095036 A B s f x y)). Qed.
Lemma lem5095038 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5095039 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term337 A B s f x) = (term342 A B s f x).
Proof. exact (MK_COMB (@lem5095038 A) (@lem5095037 A B s f x)). Qed.
Lemma lem5095040 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term336 A B s f x) = (term342 A B s f x).
Proof. exact (TRANS (@lem5095032 A B s f x) (@lem5095039 A B s f x)). Qed.
Lemma lem5095041 {A : Type'} (P : A -> Prop) : (term334 A P) = (term335 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5095042 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term343 A B s f) = (term344 A B s f).
Proof. exact (@lem5095041 A (term320 A B s f)). Qed.
Lemma lem5095043 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term345 A B s f x) = (term319 A B s f x).
Proof. exact (eq_refl (term345 A B s f x)). Qed.
Lemma lem5095044 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5095045 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term346 A B s f x) = (term336 A B s f x).
Proof. exact (MK_COMB (@lem5095044) (@lem5095043 A B s f x)). Qed.
Lemma lem5095046 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term346 A B s f x) = (term342 A B s f x).
Proof. exact (TRANS (@lem5095045 A B s f x) (@lem5095040 A B s f x)). Qed.
Lemma lem5095047 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term347 A B s f) = (term348 A B s f).
Proof. exact (fun_ext (fun x : A => @lem5095046 A B s f x)). Qed.
Lemma lem5095048 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5095049 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term344 A B s f) = (term349 A B s f).
Proof. exact (MK_COMB (@lem5095048 A) (@lem5095047 A B s f)). Qed.
Lemma lem5095050 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term343 A B s f) = (term349 A B s f).
Proof. exact (TRANS (@lem5095042 A B s f) (@lem5095049 A B s f)). Qed.
Lemma lem5095051 {A : Type'} (s : A -> Prop) (n : nat) : (term350 A s n) = (term350 A s n).
Proof. exact (eq_refl (term350 A s n)). Qed.
Lemma lem5095052 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5095053 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term351 A B s f) = (term352 A B s f).
Proof. exact (MK_COMB (@lem5095052) (@lem5095050 A B s f)). Qed.
Lemma lem5095054 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term353 A B f s n) = (term354 A B f s n).
Proof. exact (MK_COMB (@lem5095053 A B s f) (@lem5095051 A s n)). Qed.
Lemma lem5095055 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term287 A B f s n) = (term353 A B f s n).
Proof. exact (@lem17045 (term321 A B s f) (@HAS_SIZE A s n)). Qed.
Lemma lem5095056 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term287 A B f s n) = (term354 A B f s n).
Proof. exact (TRANS (@lem5095055 A B f s n) (@lem5095054 A B f s n)). Qed.
Lemma lem5095111 {A : Type'} (P : A -> Prop) (Q : Prop) : (term355 A P Q) = (term356 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5095112 {A : Type'} (P : A -> Prop) (Q : Prop) : (term355 A P Q) = (term356 A P Q).
Proof. exact (@lem5095111 A P Q). Qed.
Lemma lem5095113 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term357 A B f s n) = (term358 A B f s n).
Proof. exact (@lem5095112 A (term348 A B s f) (term350 A s n)). Qed.
Lemma lem5095114 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term359 A B s f x) = (term342 A B s f x).
Proof. exact (eq_refl (term359 A B s f x)). Qed.
Lemma lem5095115 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term360 A B s f) = (term348 A B s f).
Proof. exact (fun_ext (fun x : A => @lem5095114 A B s f x)). Qed.
Lemma lem5095116 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5095117 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term361 A B s f) = (term349 A B s f).
Proof. exact (MK_COMB (@lem5095116 A) (@lem5095115 A B s f)). Qed.
Lemma lem5095118 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5095119 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term362 A B s f) = (term352 A B s f).
Proof. exact (MK_COMB (@lem5095118) (@lem5095117 A B s f)). Qed.
Lemma lem5095120 {A : Type'} (s : A -> Prop) (n : nat) : (term350 A s n) = (term350 A s n).
Proof. exact (eq_refl (term350 A s n)). Qed.
Lemma lem5095121 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term357 A B f s n) = (term354 A B f s n).
Proof. exact (MK_COMB (@lem5095119 A B s f) (@lem5095120 A s n)). Qed.
Lemma lem5095122 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5095123 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term363 A B f s n) = (term364 A B f s n).
Proof. exact (MK_COMB (@lem5095122) (@lem5095121 A B f s n)). Qed.
Lemma lem5095124 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term359 A B s f x) = (term342 A B s f x).
Proof. exact (eq_refl (term359 A B s f x)). Qed.
Lemma lem5095125 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5095126 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term365 A B s f x) = (term366 A B s f x).
Proof. exact (MK_COMB (@lem5095125) (@lem5095124 A B s f x)). Qed.
Lemma lem5095127 {A : Type'} (s : A -> Prop) (n : nat) : (term350 A s n) = (term350 A s n).
Proof. exact (eq_refl (term350 A s n)). Qed.
Lemma lem5095128 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (n : nat) : (term367 A B f x s n) = (term368 A B f x s n).
Proof. exact (MK_COMB (@lem5095126 A B s f x) (@lem5095127 A s n)). Qed.
Lemma lem5095129 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term369 A B f s n) = (term370 A B f s n).
Proof. exact (fun_ext (fun x : A => @lem5095128 A B f x s n)). Qed.
Lemma lem5095130 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5095131 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term358 A B f s n) = (term371 A B f s n).
Proof. exact (MK_COMB (@lem5095130 A) (@lem5095129 A B f s n)). Qed.
Lemma lem5095132 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : ((term357 A B f s n) = (term358 A B f s n)) = ((term354 A B f s n) = (term371 A B f s n)).
Proof. exact (MK_COMB (@lem5095123 A B f s n) (@lem5095131 A B f s n)). Qed.
Lemma lem5095133 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term354 A B f s n) = (term371 A B f s n).
Proof. exact (EQ_MP (@lem5095132 A B f s n) (@lem5095113 A B f s n)). Qed.
Lemma lem5095135 {A : Type'} (P : A -> Prop) (Q : Prop) : (term355 A P Q) = (term356 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5095136 {A : Type'} (P : A -> Prop) (Q : Prop) : (term355 A P Q) = (term356 A P Q).
Proof. exact (@lem5095135 A P Q). Qed.
Lemma lem5095137 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (n : nat) : (term372 A B f x s n) = (term373 A B f x s n).
Proof. exact (@lem5095136 A (term341 A B s f x) (term350 A s n)). Qed.
Lemma lem5095138 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term374 A B s f x y) = (term332 A B s f x y).
Proof. exact (eq_refl (term374 A B s f x y)). Qed.
Lemma lem5095139 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term375 A B s f x) = (term341 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem5095138 A B s f x y)). Qed.
Lemma lem5095140 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5095141 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term376 A B s f x) = (term342 A B s f x).
Proof. exact (MK_COMB (@lem5095140 A) (@lem5095139 A B s f x)). Qed.
Lemma lem5095142 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5095143 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term377 A B s f x) = (term366 A B s f x).
Proof. exact (MK_COMB (@lem5095142) (@lem5095141 A B s f x)). Qed.
Lemma lem5095144 {A : Type'} (s : A -> Prop) (n : nat) : (term350 A s n) = (term350 A s n).
Proof. exact (eq_refl (term350 A s n)). Qed.
Lemma lem5095145 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (n : nat) : (term372 A B f x s n) = (term368 A B f x s n).
Proof. exact (MK_COMB (@lem5095143 A B s f x) (@lem5095144 A s n)). Qed.
Lemma lem5095146 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5095147 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (n : nat) : (term378 A B f x s n) = (term379 A B f x s n).
Proof. exact (MK_COMB (@lem5095146) (@lem5095145 A B f x s n)). Qed.
Lemma lem5095148 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term374 A B s f x y) = (term332 A B s f x y).
Proof. exact (eq_refl (term374 A B s f x y)). Qed.
Lemma lem5095149 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5095150 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term380 A B s f x y) = (term381 A B s f x y).
Proof. exact (MK_COMB (@lem5095149) (@lem5095148 A B s f x y)). Qed.
Lemma lem5095151 {A : Type'} (s : A -> Prop) (n : nat) : (term350 A s n) = (term350 A s n).
Proof. exact (eq_refl (term350 A s n)). Qed.
Lemma lem5095152 {A B : Type'} (f : A -> B) (x : A) (y : A) (s : A -> Prop) (n : nat) : (term382 A B f x y s n) = (term383 A B f x y s n).
Proof. exact (MK_COMB (@lem5095150 A B s f x y) (@lem5095151 A s n)). Qed.
Lemma lem5095153 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (n : nat) : (term384 A B f x s n) = (term385 A B f x s n).
Proof. exact (fun_ext (fun y : A => @lem5095152 A B f x y s n)). Qed.
Lemma lem5095154 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5095155 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (n : nat) : (term373 A B f x s n) = (term386 A B f x s n).
Proof. exact (MK_COMB (@lem5095154 A) (@lem5095153 A B f x s n)). Qed.
Lemma lem5095156 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (n : nat) : ((term372 A B f x s n) = (term373 A B f x s n)) = ((term368 A B f x s n) = (term386 A B f x s n)).
Proof. exact (MK_COMB (@lem5095147 A B f x s n) (@lem5095155 A B f x s n)). Qed.
Lemma lem5095157 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (n : nat) : (term368 A B f x s n) = (term386 A B f x s n).
Proof. exact (EQ_MP (@lem5095156 A B f x s n) (@lem5095137 A B f x s n)). Qed.
Lemma lem5095158 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term370 A B f s n) = (term387 A B f s n).
Proof. exact (fun_ext (fun x : A => @lem5095157 A B f x s n)). Qed.
Lemma lem5095159 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5095160 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term371 A B f s n) = (term388 A B f s n).
Proof. exact (MK_COMB (@lem5095159 A) (@lem5095158 A B f s n)). Qed.
Lemma lem5095162 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term354 A B f s n) = (term388 A B f s n).
Proof. exact (TRANS (@lem5095133 A B f s n) (@lem5095160 A B f s n)). Qed.
Lemma lem5095163 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term287 A B f s n) = (term388 A B f s n).
Proof. exact (TRANS (@lem5095056 A B f s n) (@lem5095162 A B f s n)). Qed.
Lemma lem5095164 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term287 A B f s n) : term388 A B f s n.
Proof. exact (EQ_MP (@lem5095163 A B f s n) (@lem5094875 A B f s n h1)). Qed.
Lemma lem5095165 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (n : nat) (h1 : term386 A B f x s n) : term386 A B f x s n.
Proof. exact (h1). Qed.
Lemma lem5095166 {A B : Type'} (f : A -> B) (x : A) (y : A) (s : A -> Prop) (n : nat) (h1 : term383 A B f x y s n) : term383 A B f x y s n.
Proof. exact (h1). Qed.
Lemma lem5095167 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem5095168 {A B : Type'} (g : B -> A) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem5095173 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5095175 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5095173 A B f x). Qed.
Lemma lem5095176 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term59 A B g f x) = (term389 A B g f x).
Proof. exact (MK_COMB (@lem5095168 A B g) (@lem5095175 A B f x)). Qed.
Lemma lem5095177 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5095178 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term390 A B g f x) = (term391 A B g f x).
Proof. exact (MK_COMB (@lem5095167 A) (@lem5095176 A B g f x)). Qed.
Lemma lem5095179 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : ((term59 A B g f x) = x) = ((term389 A B g f x) = x).
Proof. exact (MK_COMB (@lem5095178 A B g f x) (@lem5095177 A x)). Qed.
Lemma lem5095180 {B : Type'} : (@IN B) = (@IN B).
Proof. exact (eq_refl (@IN B)). Qed.
Lemma lem5095185 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5095187 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5095185 A B f x). Qed.
Lemma lem5095192 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (@IMAGE A B f s).
Proof. exact (eq_refl (@IMAGE A B f s)). Qed.
Lemma lem5095193 {A B : Type'} (f : A -> B) (x : A) : (term392 A B f x) = (term393 A B f x).
Proof. exact (MK_COMB (@lem5095180 B) (@lem5095187 A B f x)). Qed.
Lemma lem5095194 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term394 A B x f s) = (term395 A B x f s).
Proof. exact (MK_COMB (@lem5095193 A B f x) (@lem5095192 A B f s)). Qed.
Lemma lem5095195 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5095196 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term396 A B x f s) = (term397 A B x f s).
Proof. exact (MK_COMB (@lem5095195) (@lem5095194 A B x f s)). Qed.
Lemma lem5095197 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term328 A B s g f x) = (term398 A B s g f x).
Proof. exact (MK_COMB (@lem5095196 A B x f s) (@lem5095179 A B g f x)). Qed.
Lemma lem5095206 {A : Type'} (x : A) (s : A -> Prop) : (term399 A x s) = (term399 A x s).
Proof. exact (eq_refl (term399 A x s)). Qed.
Lemma lem5095207 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term327 A B s g f x) = (term400 A B s g f x).
Proof. exact (MK_COMB (@lem5095206 A x s) (@lem5095197 A B s g f x)). Qed.
Lemma lem5095208 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term329 A B s g f) = (term401 A B s g f).
Proof. exact (fun_ext (fun x : A => @lem5095207 A B s g f x)). Qed.
Lemma lem5095209 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5095210 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term330 A B s g f) = (term402 A B s g f).
Proof. exact (MK_COMB (@lem5095209 A) (@lem5095208 A B s g f)). Qed.
Lemma lem5095211 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term23 A B s g f) : term402 A B s g f.
Proof. exact (EQ_MP (@lem5095210 A B s g f) (@lem5094942 A B s g f h1)). Qed.
Lemma lem5095259 {A : Type'} (s : A -> Prop) (n : nat) (h1 : @HAS_SIZE A s n) : @HAS_SIZE A s n.
Proof. exact (h1). Qed.
Lemma lem5095266 {A : Type'} (s : A -> Prop) (n : nat) : (term350 A s n) = (term350 A s n).
Proof. exact (eq_refl (term350 A s n)). Qed.
Lemma lem5095273 {A : Type'} (x : A) (y : A) : (term232 A x y) = (term232 A x y).
Proof. exact (eq_refl (term232 A x y)). Qed.
Lemma lem5095274 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5095279 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5095281 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5095279 A B f x). Qed.
Lemma lem5095286 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5095287 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5095286 A B f x). Qed.
Lemma lem5095289 {A B : Type'} (f : A -> B) (y : A) : (f y) = (@I (A -> B) f y).
Proof. exact (@lem5095287 A B f y). Qed.
Lemma lem5095290 {A B : Type'} (f : A -> B) (x : A) : (term403 A B f x) = (term404 A B f x).
Proof. exact (MK_COMB (@lem5095274 B) (@lem5095281 A B f x)). Qed.
Lemma lem5095291 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((@I (A -> B) f x) = (@I (A -> B) f y)).
Proof. exact (MK_COMB (@lem5095290 A B f x) (@lem5095289 A B f y)). Qed.
Lemma lem5095298 {A : Type'} (y : A) (s : A -> Prop) : (term405 A y s) = (term405 A y s).
Proof. exact (eq_refl (term405 A y s)). Qed.
Lemma lem5095299 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term406 A B s x f y) = (term407 A B s x f y).
Proof. exact (MK_COMB (@lem5095298 A y s) (@lem5095291 A B x f y)). Qed.
Lemma lem5095306 {A : Type'} (x : A) (s : A -> Prop) : (term405 A x s) = (term405 A x s).
Proof. exact (eq_refl (term405 A x s)). Qed.
Lemma lem5095307 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term333 A B s x f y) = (term408 A B s x f y).
Proof. exact (MK_COMB (@lem5095306 A x s) (@lem5095299 A B s x f y)). Qed.
Lemma lem5095308 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5095309 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term409 A B s x f y) = (term410 A B s x f y).
Proof. exact (MK_COMB (@lem5095308) (@lem5095307 A B s x f y)). Qed.
Lemma lem5095310 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term332 A B s f x y) = (term411 A B s f x y).
Proof. exact (MK_COMB (@lem5095309 A B s x f y) (@lem5095273 A x y)). Qed.
Lemma lem5095311 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5095312 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term381 A B s f x y) = (term412 A B s f x y).
Proof. exact (MK_COMB (@lem5095311) (@lem5095310 A B s f x y)). Qed.
Lemma lem5095313 {A B : Type'} (f : A -> B) (x : A) (y : A) (s : A -> Prop) (n : nat) : (term383 A B f x y s n) = (term413 A B f x y s n).
Proof. exact (MK_COMB (@lem5095312 A B s f x y) (@lem5095266 A s n)). Qed.
Lemma lem5095314 {A B : Type'} (f : A -> B) (x : A) (y : A) (s : A -> Prop) (n : nat) (h1 : term383 A B f x y s n) : term413 A B f x y s n.
Proof. exact (EQ_MP (@lem5095313 A B f x y s n) (@lem5095166 A B f x y s n h1)). Qed.
Lemma lem5095315 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term411 A B s f x y) : term411 A B s f x y.
Proof. exact (h1). Qed.
Lemma lem5095318 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term411 A B s f x y) : term408 A B s x f y.
Proof. exact (proj1 (@lem5095315 A B s f x y h1)). Qed.
Lemma lem5095319 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term411 A B s f x y) : term407 A B s x f y.
Proof. exact (proj2 (@lem5095318 A B s f x y h1)). Qed.
Lemma lem5095340 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term400 A B s g f x) = (term414 A B s g f x).
Proof. exact (@lem19490 (term395 A B x f s) (term415 A x s) ((term389 A B g f x) = x)). Qed.
Lemma lem5095341 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term401 A B s g f) = (term416 A B s g f).
Proof. exact (fun_ext (fun x : A => @lem5095340 A B s g f x)). Qed.
Lemma lem5095342 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5095344 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term402 A B s g f) = (term417 A B s g f).
Proof. exact (MK_COMB (@lem5095342 A) (@lem5095341 A B s g f)). Qed.
Lemma lem5095345 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term23 A B s g f) : term417 A B s g f.
Proof. exact (EQ_MP (@lem5095344 A B s g f) (@lem5095211 A B s g f h1)). Qed.
Lemma lem5095438 {A : Type'} (s : A -> Prop) (n : nat) (h1 : @HAS_SIZE A s n) : @HAS_SIZE A s n.
Proof. exact (h1). Qed.
Lemma lem5095442 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term350 A s n) : term350 A s n.
Proof. exact (h1). Qed.
Lemma lem5095443 {A B : Type'} (_66289 : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term23 A B s g f) : term418 A B s g f _66289.
Proof. exact (@lem5095345 A B s g f h1 _66289). Qed.
Lemma lem5095444 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (_66289 : A) : (term418 A B s g f _66289) = (term414 A B s g f _66289).
Proof. exact (eq_refl (term418 A B s g f _66289)). Qed.
Lemma lem5095445 {A B : Type'} (_66289 : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term23 A B s g f) : term414 A B s g f _66289.
Proof. exact (EQ_MP (@lem5095444 A B s g f _66289) (@lem5095443 A B _66289 s g f h1)). Qed.
Lemma lem5095466 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term411 A B s f x y) : term232 A x y.
Proof. exact (proj2 (@lem5095315 A B s f x y h1)). Qed.
Lemma lem5095496 {A B : Type'} (_66289 : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term23 A B s g f) : term419 A B s g f _66289.
Proof. exact (proj2 (@lem5095445 A B _66289 s g f h1)). Qed.
Lemma lem5095498 {A : Type'} (s : A -> Prop) (n : nat) (h1 : @HAS_SIZE A s n) : @HAS_SIZE A s n.
Proof. exact (h1). Qed.
Lemma lem5095500 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term350 A s n) : term350 A s n.
Proof. exact (h1). Qed.
Lemma lem5095597 {A B : Type'} (g : B -> A) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem5095598 {B : Type'} (_66309 : B) (_66310 : B) (h1 : _66309 = _66310) : _66309 = _66310.
Proof. exact (h1). Qed.
Lemma lem5095599 {A B : Type'} (g : B -> A) (_66309 : B) (_66310 : B) (h1 : _66309 = _66310) : (g _66309) = (g _66310).
Proof. exact (MK_COMB (@lem5095597 A B g) (@lem5095598 B _66309 _66310 h1)). Qed.
Lemma lem5095600 {A B : Type'} (_66309 : B) (g : B -> A) (_66310 : B) : term420 A B _66309 g _66310.
Proof. exact (fun h0 : _66309 = _66310 => @lem5095599 A B g _66309 _66310 h0). Qed.
Lemma lem5095602 (a : Prop) (b : Prop) : (a -> b) = (term421 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5095603 {A B : Type'} (_66309 : B) (g : B -> A) (_66310 : B) : (term420 A B _66309 g _66310) = (term422 A B _66309 g _66310).
Proof. exact (@lem5095602 (_66309 = _66310) ((g _66309) = (g _66310))). Qed.
Lemma lem5095604 {A B : Type'} (_66309 : B) (g : B -> A) (_66310 : B) : term422 A B _66309 g _66310.
Proof. exact (EQ_MP (@lem5095603 A B _66309 g _66310) (@lem5095600 A B _66309 g _66310)). Qed.
Lemma lem5095625 {A : Type'} (x : A) (y : A) (z : A) : term215 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem5095633 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term411 A B s f x y) : (@I (A -> B) f x) = (@I (A -> B) f y).
Proof. exact (proj2 (@lem5095319 A B s f x y h1)). Qed.
Lemma lem5095634 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term411 A B s f x y) : term423 A B x f y.
Proof. exact (fun h0 : term424 A B x f y => @lem5095633 A B s f x y h1). Qed.
Lemma lem5095636 (p : Prop) : (term217 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5095637 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term423 A B x f y) = ((@I (A -> B) f x) = (@I (A -> B) f y)).
Proof. exact (@lem5095636 ((@I (A -> B) f x) = (@I (A -> B) f y))). Qed.
Lemma lem5095638 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term411 A B s f x y) : (@I (A -> B) f x) = (@I (A -> B) f y).
Proof. exact (EQ_MP (@lem5095637 A B x f y) (@lem5095634 A B s f x y h1)). Qed.
Lemma lem5095644 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5095645 {A B : Type'} (g : B -> A) (_66309 : B) (_66310 : B) : (term422 A B _66309 g _66310) = (term425 A B g _66309 _66310).
Proof. exact (@lem5095644 ((g _66309) = (g _66310)) (term232 B _66309 _66310)). Qed.
Lemma lem5095655 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5095656 {A B : Type'} (g : B -> A) (_66309 : B) (_66310 : B) : (term426 A B _66309 g _66310) = (term427 A B g _66309 _66310).
Proof. exact (MK_COMB (@lem5095655) (@lem5095645 A B g _66309 _66310)). Qed.
Lemma lem5095666 {A B : Type'} (g : B -> A) (_66309 : B) (_66310 : B) : (term425 A B g _66309 _66310) = (term425 A B g _66309 _66310).
Proof. exact (eq_refl (term425 A B g _66309 _66310)). Qed.
Lemma lem5095667 {A B : Type'} (g : B -> A) (_66309 : B) (_66310 : B) : ((term422 A B _66309 g _66310) = (term425 A B g _66309 _66310)) = ((term425 A B g _66309 _66310) = (term425 A B g _66309 _66310)).
Proof. exact (MK_COMB (@lem5095656 A B g _66309 _66310) (@lem5095666 A B g _66309 _66310)). Qed.
Lemma lem5095669 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5095670 (x : Prop) : (x = x) = True.
Proof. exact (@lem5095669 Prop x). Qed.
Lemma lem5095671 {A B : Type'} (g : B -> A) (_66309 : B) (_66310 : B) : ((term425 A B g _66309 _66310) = (term425 A B g _66309 _66310)) = True.
Proof. exact (@lem5095670 (term425 A B g _66309 _66310)). Qed.
Lemma lem5095672 {A B : Type'} (g : B -> A) (_66309 : B) (_66310 : B) : ((term422 A B _66309 g _66310) = (term425 A B g _66309 _66310)) = True.
Proof. exact (TRANS (@lem5095667 A B g _66309 _66310) (@lem5095671 A B g _66309 _66310)). Qed.
Lemma lem5095673 {A B : Type'} (g : B -> A) (_66309 : B) (_66310 : B) : True = ((term422 A B _66309 g _66310) = (term425 A B g _66309 _66310)).
Proof. exact (SYM (@lem5095672 A B g _66309 _66310)). Qed.
Lemma lem5095674 {A B : Type'} (g : B -> A) (_66309 : B) (_66310 : B) : (term422 A B _66309 g _66310) = (term425 A B g _66309 _66310).
Proof. exact (EQ_MP (@lem5095673 A B g _66309 _66310) (@lem0)). Qed.
Lemma lem5095675 {A B : Type'} (g : B -> A) (_66309 : B) (_66310 : B) : term425 A B g _66309 _66310.
Proof. exact (EQ_MP (@lem5095674 A B g _66309 _66310) (@lem5095604 A B _66309 g _66310)). Qed.
Lemma lem5095677 (b : Prop) (a : Prop) : (a \/ b) = (term221 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5095678 {A B : Type'} (_66309 : B) (g : B -> A) (_66310 : B) : (term425 A B g _66309 _66310) = (term428 A B _66309 g _66310).
Proof. exact (@lem5095677 (term232 B _66309 _66310) ((g _66309) = (g _66310))). Qed.
Lemma lem5095680 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5095681 {B : Type'} (_66309 : B) (_66310 : B) : (term245 B _66309 _66310) = (_66309 = _66310).
Proof. exact (@lem5095680 (_66309 = _66310)). Qed.
Lemma lem5095682 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5095683 {B : Type'} (_66309 : B) (_66310 : B) : (term429 B _66309 _66310) = (term430 B _66309 _66310).
Proof. exact (MK_COMB (@lem5095682) (@lem5095681 B _66309 _66310)). Qed.
Lemma lem5095684 {A B : Type'} (_66309 : B) (g : B -> A) (_66310 : B) : ((g _66309) = (g _66310)) = ((g _66309) = (g _66310)).
Proof. exact (eq_refl ((g _66309) = (g _66310))). Qed.
Lemma lem5095685 {A B : Type'} (_66309 : B) (g : B -> A) (_66310 : B) : (term428 A B _66309 g _66310) = (term420 A B _66309 g _66310).
Proof. exact (MK_COMB (@lem5095683 B _66309 _66310) (@lem5095684 A B _66309 g _66310)). Qed.
Lemma lem5095686 {A B : Type'} (_66309 : B) (g : B -> A) (_66310 : B) : (term425 A B g _66309 _66310) = (term420 A B _66309 g _66310).
Proof. exact (TRANS (@lem5095678 A B _66309 g _66310) (@lem5095685 A B _66309 g _66310)). Qed.
Lemma lem5095689 {A B : Type'} (_66309 : B) (g : B -> A) (_66310 : B) : term420 A B _66309 g _66310.
Proof. exact (EQ_MP (@lem5095686 A B _66309 g _66310) (@lem5095675 A B g _66309 _66310)). Qed.
Lemma lem5095690 {A B : Type'} (_66309 : B) (g : B -> A) (_66310 : B) : term420 A B _66309 g _66310.
Proof. exact (@lem5095689 A B _66309 g _66310). Qed.
Lemma lem5095691 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (y : A) : term431 A B x g f y.
Proof. exact (@lem5095690 A B (@I (A -> B) f x) g (@I (A -> B) f y)). Qed.
Lemma lem5095694 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term411 A B s f x y) : (term389 A B g f x) = (term389 A B g f y).
Proof. exact (@lem5095691 A B x g f y (@lem5095638 A B s f x y h1)). Qed.
Lemma lem5095695 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term411 A B s f x y) : term432 A B x g f y.
Proof. exact (fun h0 : term433 A B x g f y => @lem5095694 A B g s f x y h1). Qed.
Lemma lem5095697 (p : Prop) : (term217 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5095698 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (y : A) : (term432 A B x g f y) = ((term389 A B g f x) = (term389 A B g f y)).
Proof. exact (@lem5095697 ((term389 A B g f x) = (term389 A B g f y))). Qed.
Lemma lem5095699 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term411 A B s f x y) : (term389 A B g f x) = (term389 A B g f y).
Proof. exact (EQ_MP (@lem5095698 A B x g f y) (@lem5095695 A B g s f x y h1)). Qed.
Lemma lem5095701 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term411 A B s f x y) : @IN A x s.
Proof. exact (proj1 (@lem5095318 A B s f x y h1)). Qed.
Lemma lem5095702 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term411 A B s f x y) : term434 A x s.
Proof. exact (fun h0 : term415 A x s => @lem5095701 A B s f x y h1). Qed.
Lemma lem5095704 (p : Prop) : (term217 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5095705 {A : Type'} (x : A) (s : A -> Prop) : (term434 A x s) = (@IN A x s).
Proof. exact (@lem5095704 (@IN A x s)). Qed.
Lemma lem5095706 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term411 A B s f x y) : @IN A x s.
Proof. exact (EQ_MP (@lem5095705 A x s) (@lem5095702 A B s f x y h1)). Qed.
Lemma lem5095712 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5095713 {A B : Type'} (g : B -> A) (f : A -> B) (_66289 : A) (s : A -> Prop) : (term419 A B s g f _66289) = (term435 A B g f _66289 s).
Proof. exact (@lem5095712 ((term389 A B g f _66289) = _66289) (term415 A _66289 s)). Qed.
Lemma lem5095721 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5095722 {A B : Type'} (g : B -> A) (f : A -> B) (_66289 : A) (s : A -> Prop) : (term436 A B s g f _66289) = (term437 A B g f _66289 s).
Proof. exact (MK_COMB (@lem5095721) (@lem5095713 A B g f _66289 s)). Qed.
Lemma lem5095730 {A B : Type'} (g : B -> A) (f : A -> B) (_66289 : A) (s : A -> Prop) : (term435 A B g f _66289 s) = (term435 A B g f _66289 s).
Proof. exact (eq_refl (term435 A B g f _66289 s)). Qed.
Lemma lem5095731 {A B : Type'} (g : B -> A) (f : A -> B) (_66289 : A) (s : A -> Prop) : ((term419 A B s g f _66289) = (term435 A B g f _66289 s)) = ((term435 A B g f _66289 s) = (term435 A B g f _66289 s)).
Proof. exact (MK_COMB (@lem5095722 A B g f _66289 s) (@lem5095730 A B g f _66289 s)). Qed.
Lemma lem5095733 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5095734 (x : Prop) : (x = x) = True.
Proof. exact (@lem5095733 Prop x). Qed.
Lemma lem5095735 {A B : Type'} (g : B -> A) (f : A -> B) (_66289 : A) (s : A -> Prop) : ((term435 A B g f _66289 s) = (term435 A B g f _66289 s)) = True.
Proof. exact (@lem5095734 (term435 A B g f _66289 s)). Qed.
Lemma lem5095736 {A B : Type'} (g : B -> A) (f : A -> B) (_66289 : A) (s : A -> Prop) : ((term419 A B s g f _66289) = (term435 A B g f _66289 s)) = True.
Proof. exact (TRANS (@lem5095731 A B g f _66289 s) (@lem5095735 A B g f _66289 s)). Qed.
Lemma lem5095737 {A B : Type'} (g : B -> A) (f : A -> B) (_66289 : A) (s : A -> Prop) : True = ((term419 A B s g f _66289) = (term435 A B g f _66289 s)).
Proof. exact (SYM (@lem5095736 A B g f _66289 s)). Qed.
Lemma lem5095738 {A B : Type'} (g : B -> A) (f : A -> B) (_66289 : A) (s : A -> Prop) : (term419 A B s g f _66289) = (term435 A B g f _66289 s).
Proof. exact (EQ_MP (@lem5095737 A B g f _66289 s) (@lem0)). Qed.
Lemma lem5095739 {A B : Type'} (_66289 : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term23 A B s g f) : term435 A B g f _66289 s.
Proof. exact (EQ_MP (@lem5095738 A B g f _66289 s) (@lem5095496 A B _66289 s g f h1)). Qed.
Lemma lem5095741 (b : Prop) (a : Prop) : (a \/ b) = (term221 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5095742 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (_66289 : A) : (term435 A B g f _66289 s) = (term438 A B s g f _66289).
Proof. exact (@lem5095741 (term415 A _66289 s) ((term389 A B g f _66289) = _66289)). Qed.
Lemma lem5095744 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5095745 {A : Type'} (_66289 : A) (s : A -> Prop) : (term439 A _66289 s) = (@IN A _66289 s).
Proof. exact (@lem5095744 (@IN A _66289 s)). Qed.
Lemma lem5095746 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5095747 {A : Type'} (_66289 : A) (s : A -> Prop) : (term440 A _66289 s) = (term39 A _66289 s).
Proof. exact (MK_COMB (@lem5095746) (@lem5095745 A _66289 s)). Qed.
Lemma lem5095748 {A B : Type'} (g : B -> A) (f : A -> B) (_66289 : A) : ((term389 A B g f _66289) = _66289) = ((term389 A B g f _66289) = _66289).
Proof. exact (eq_refl ((term389 A B g f _66289) = _66289)). Qed.
Lemma lem5095749 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (_66289 : A) : (term438 A B s g f _66289) = (term441 A B s g f _66289).
Proof. exact (MK_COMB (@lem5095747 A _66289 s) (@lem5095748 A B g f _66289)). Qed.
Lemma lem5095750 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (_66289 : A) : (term435 A B g f _66289 s) = (term441 A B s g f _66289).
Proof. exact (TRANS (@lem5095742 A B s g f _66289) (@lem5095749 A B s g f _66289)). Qed.
Lemma lem5095753 {A B : Type'} (_66289 : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term23 A B s g f) : term441 A B s g f _66289.
Proof. exact (EQ_MP (@lem5095750 A B s g f _66289) (@lem5095739 A B _66289 s g f h1)). Qed.
Lemma lem5095754 {A B : Type'} (_66289 : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term23 A B s g f) : term441 A B s g f _66289.
Proof. exact (@lem5095753 A B _66289 s g f h1). Qed.
Lemma lem5095755 {A B : Type'} (x : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term23 A B s g f) : term441 A B s g f x.
Proof. exact (@lem5095754 A B x s g f h1). Qed.
Lemma lem5095758 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term23 A B s g f) (h2 : term411 A B s f x y) : (term389 A B g f x) = x.
Proof. exact (@lem5095755 A B x s g f h1 (@lem5095706 A B s f x y h2)). Qed.
Lemma lem5095759 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term23 A B s g f) (h2 : term411 A B s f x y) : term442 A B g f x.
Proof. exact (fun h0 : term443 A B g f x => @lem5095758 A B g s f x y h1 h2). Qed.
Lemma lem5095761 (p : Prop) : (term217 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5095762 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term442 A B g f x) = ((term389 A B g f x) = x).
Proof. exact (@lem5095761 ((term389 A B g f x) = x)). Qed.
Lemma lem5095763 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term23 A B s g f) (h2 : term411 A B s f x y) : (term389 A B g f x) = x.
Proof. exact (EQ_MP (@lem5095762 A B g f x) (@lem5095759 A B g s f x y h1 h2)). Qed.
Lemma lem5095781 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5095782 {A : Type'} (y : A) (x : A) (z : A) : (term230 A x y z) = (term231 A y x z).
Proof. exact (@lem5095781 (y = z) (term232 A x z)). Qed.
Lemma lem5095792 {A : Type'} (x : A) (y : A) : (term233 A x y) = (term233 A x y).
Proof. exact (eq_refl (term233 A x y)). Qed.
Lemma lem5095793 {A : Type'} (y : A) (x : A) (z : A) : (term215 A x y z) = (term234 A y x z).
Proof. exact (MK_COMB (@lem5095792 A x y) (@lem5095782 A y x z)). Qed.
Lemma lem5095797 (q : Prop) (p : Prop) (r : Prop) : (term235 p q r) = (term235 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5095798 {A : Type'} (y : A) (x : A) (z : A) : (term234 A y x z) = (term236 A y x z).
Proof. exact (@lem5095797 (y = z) (term232 A x y) (term232 A x z)). Qed.
Lemma lem5095820 {A : Type'} (y : A) (x : A) (z : A) : (term215 A x y z) = (term236 A y x z).
Proof. exact (TRANS (@lem5095793 A y x z) (@lem5095798 A y x z)). Qed.
Lemma lem5095821 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5095822 {A : Type'} (y : A) (x : A) (z : A) : (term237 A x y z) = (term238 A y x z).
Proof. exact (MK_COMB (@lem5095821) (@lem5095820 A y x z)). Qed.
Lemma lem5095844 {A : Type'} (y : A) (x : A) (z : A) : (term236 A y x z) = (term236 A y x z).
Proof. exact (eq_refl (term236 A y x z)). Qed.
Lemma lem5095845 {A : Type'} (y : A) (x : A) (z : A) : ((term215 A x y z) = (term236 A y x z)) = ((term236 A y x z) = (term236 A y x z)).
Proof. exact (MK_COMB (@lem5095822 A y x z) (@lem5095844 A y x z)). Qed.
Lemma lem5095847 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5095848 (x : Prop) : (x = x) = True.
Proof. exact (@lem5095847 Prop x). Qed.
Lemma lem5095849 {A : Type'} (y : A) (x : A) (z : A) : ((term236 A y x z) = (term236 A y x z)) = True.
Proof. exact (@lem5095848 (term236 A y x z)). Qed.
Lemma lem5095850 {A : Type'} (y : A) (x : A) (z : A) : ((term215 A x y z) = (term236 A y x z)) = True.
Proof. exact (TRANS (@lem5095845 A y x z) (@lem5095849 A y x z)). Qed.
Lemma lem5095851 {A : Type'} (y : A) (x : A) (z : A) : True = ((term215 A x y z) = (term236 A y x z)).
Proof. exact (SYM (@lem5095850 A y x z)). Qed.
Lemma lem5095852 {A : Type'} (y : A) (x : A) (z : A) : (term215 A x y z) = (term236 A y x z).
Proof. exact (EQ_MP (@lem5095851 A y x z) (@lem0)). Qed.
Lemma lem5095853 {A : Type'} (y : A) (x : A) (z : A) : term236 A y x z.
Proof. exact (EQ_MP (@lem5095852 A y x z) (@lem5095625 A x y z)). Qed.
Lemma lem5095855 (b : Prop) (a : Prop) : (a \/ b) = (term221 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5095856 {A : Type'} (x : A) (y : A) (z : A) : (term236 A y x z) = (term239 A x y z).
Proof. exact (@lem5095855 (term240 A y x z) (y = z)). Qed.
Lemma lem5095858 (a : Prop) (b : Prop) : (term241 a b) = (term242 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5095859 {A : Type'} (y : A) (x : A) (z : A) : (term243 A y x z) = (term244 A y x z).
Proof. exact (@lem5095858 (term232 A x y) (term232 A x z)). Qed.
Lemma lem5095861 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5095862 {A : Type'} (x : A) (y : A) : (term245 A x y) = (x = y).
Proof. exact (@lem5095861 (x = y)). Qed.
Lemma lem5095863 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5095864 {A : Type'} (x : A) (y : A) : (term246 A x y) = (term247 A x y).
Proof. exact (MK_COMB (@lem5095863) (@lem5095862 A x y)). Qed.
Lemma lem5095866 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5095867 {A : Type'} (x : A) (z : A) : (term245 A x z) = (x = z).
Proof. exact (@lem5095866 (x = z)). Qed.
Lemma lem5095868 {A : Type'} (y : A) (x : A) (z : A) : (term244 A y x z) = (term248 A y x z).
Proof. exact (MK_COMB (@lem5095864 A x y) (@lem5095867 A x z)). Qed.
Lemma lem5095869 {A : Type'} (y : A) (x : A) (z : A) : (term243 A y x z) = (term248 A y x z).
Proof. exact (TRANS (@lem5095859 A y x z) (@lem5095868 A y x z)). Qed.
Lemma lem5095870 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5095871 {A : Type'} (y : A) (x : A) (z : A) : (term249 A y x z) = (term250 A y x z).
Proof. exact (MK_COMB (@lem5095870) (@lem5095869 A y x z)). Qed.
Lemma lem5095872 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5095873 {A : Type'} (x : A) (y : A) (z : A) : (term239 A x y z) = (term251 A x y z).
Proof. exact (MK_COMB (@lem5095871 A y x z) (@lem5095872 A y z)). Qed.
Lemma lem5095874 {A : Type'} (x : A) (y : A) (z : A) : (term236 A y x z) = (term251 A x y z).
Proof. exact (TRANS (@lem5095856 A x y z) (@lem5095873 A x y z)). Qed.
Lemma lem5095876 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term23 A B s g f) (h2 : term411 A B s f x y) : term444 A B y g f x.
Proof. exact (conj (@lem5095699 A B g s f x y h2) (@lem5095763 A B g s f x y h1 h2)). Qed.
Lemma lem5095878 {A : Type'} (x : A) (y : A) (z : A) : term251 A x y z.
Proof. exact (EQ_MP (@lem5095874 A x y z) (@lem5095853 A y x z)). Qed.
Lemma lem5095879 {A : Type'} (x : A) (y : A) (z : A) : term251 A x y z.
Proof. exact (@lem5095878 A x y z). Qed.
Lemma lem5095880 {A B : Type'} (g : B -> A) (f : A -> B) (y : A) (x : A) : term445 A B g f y x.
Proof. exact (@lem5095879 A (term389 A B g f x) (term389 A B g f y) x). Qed.
Lemma lem5095883 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term23 A B s g f) (h2 : term411 A B s f x y) : (term389 A B g f y) = x.
Proof. exact (@lem5095880 A B g f y x (@lem5095876 A B g s f x y h1 h2)). Qed.
Lemma lem5095884 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term23 A B s g f) (h2 : term411 A B s f x y) : term446 A B g f y x.
Proof. exact (fun h0 : term447 A B g f y x => @lem5095883 A B g s f x y h1 h2). Qed.
Lemma lem5095886 (p : Prop) : (term217 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5095887 {A B : Type'} (g : B -> A) (f : A -> B) (y : A) (x : A) : (term446 A B g f y x) = ((term389 A B g f y) = x).
Proof. exact (@lem5095886 ((term389 A B g f y) = x)). Qed.
Lemma lem5095888 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term23 A B s g f) (h2 : term411 A B s f x y) : (term389 A B g f y) = x.
Proof. exact (EQ_MP (@lem5095887 A B g f y x) (@lem5095884 A B g s f x y h1 h2)). Qed.
Lemma lem5095890 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term411 A B s f x y) : @IN A y s.
Proof. exact (proj1 (@lem5095319 A B s f x y h1)). Qed.
Lemma lem5095891 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term411 A B s f x y) : term434 A y s.
Proof. exact (fun h0 : term415 A y s => @lem5095890 A B s f x y h1). Qed.
Lemma lem5095893 (p : Prop) : (term217 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5095894 {A : Type'} (y : A) (s : A -> Prop) : (term434 A y s) = (@IN A y s).
Proof. exact (@lem5095893 (@IN A y s)). Qed.
Lemma lem5095895 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term411 A B s f x y) : @IN A y s.
Proof. exact (EQ_MP (@lem5095894 A y s) (@lem5095891 A B s f x y h1)). Qed.
Lemma lem5095897 {A B : Type'} (_66289 : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term23 A B s g f) : term441 A B s g f _66289.
Proof. exact (EQ_MP (@lem5095750 A B s g f _66289) (@lem5095739 A B _66289 s g f h1)). Qed.
Lemma lem5095898 {A B : Type'} (_66289 : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term23 A B s g f) : term441 A B s g f _66289.
Proof. exact (@lem5095897 A B _66289 s g f h1). Qed.
Lemma lem5095899 {A B : Type'} (y : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term23 A B s g f) : term441 A B s g f y.
Proof. exact (@lem5095898 A B y s g f h1). Qed.
Lemma lem5095902 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term23 A B s g f) (h2 : term411 A B s f x y) : (term389 A B g f y) = y.
Proof. exact (@lem5095899 A B y s g f h1 (@lem5095895 A B s f x y h2)). Qed.
Lemma lem5095903 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term23 A B s g f) (h2 : term411 A B s f x y) : term442 A B g f y.
Proof. exact (fun h0 : term443 A B g f y => @lem5095902 A B g s f x y h1 h2). Qed.
Lemma lem5095905 (p : Prop) : (term217 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5095906 {A B : Type'} (g : B -> A) (f : A -> B) (y : A) : (term442 A B g f y) = ((term389 A B g f y) = y).
Proof. exact (@lem5095905 ((term389 A B g f y) = y)). Qed.
Lemma lem5095907 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term23 A B s g f) (h2 : term411 A B s f x y) : (term389 A B g f y) = y.
Proof. exact (EQ_MP (@lem5095906 A B g f y) (@lem5095903 A B g s f x y h1 h2)). Qed.
Lemma lem5095908 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term23 A B s g f) (h2 : term411 A B s f x y) : term448 A B x g f y.
Proof. exact (conj (@lem5095888 A B g s f x y h1 h2) (@lem5095907 A B g s f x y h1 h2)). Qed.
Lemma lem5095910 {A : Type'} (x : A) (y : A) (z : A) : term251 A x y z.
Proof. exact (EQ_MP (@lem5095874 A x y z) (@lem5095853 A y x z)). Qed.
Lemma lem5095911 {A : Type'} (x : A) (y : A) (z : A) : term251 A x y z.
Proof. exact (@lem5095910 A x y z). Qed.
Lemma lem5095912 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) (y : A) : term449 A B g f x y.
Proof. exact (@lem5095911 A (term389 A B g f y) x y). Qed.
Lemma lem5095915 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term23 A B s g f) (h2 : term411 A B s f x y) : x = y.
Proof. exact (@lem5095912 A B g f x y (@lem5095908 A B g s f x y h1 h2)). Qed.
Lemma lem5095916 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term23 A B s g f) (h2 : term411 A B s f x y) : term450 A x y.
Proof. exact (fun h0 : term232 A x y => @lem5095915 A B g s f x y h1 h2). Qed.
Lemma lem5095918 (p : Prop) : (term217 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5095919 {A : Type'} (x : A) (y : A) : (term450 A x y) = (x = y).
Proof. exact (@lem5095918 (x = y)). Qed.
Lemma lem5095920 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term23 A B s g f) (h2 : term411 A B s f x y) : x = y.
Proof. exact (EQ_MP (@lem5095919 A x y) (@lem5095916 A B g s f x y h1 h2)). Qed.
Lemma lem5095923 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5095925 {A : Type'} (x : A) (y : A) : (term232 A x y) = (term451 A x y).
Proof. exact (@lem5095923 (x = y)). Qed.
Lemma lem5095928 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term411 A B s f x y) : term451 A x y.
Proof. exact (EQ_MP (@lem5095925 A x y) (@lem5095466 A B s f x y h1)). Qed.
Lemma lem5095931 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term23 A B s g f) (h2 : term411 A B s f x y) : False.
Proof. exact (@lem5095928 A B s f x y h2 (@lem5095920 A B g s f x y h1 h2)). Qed.
Lemma lem5095932 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term23 A B s g f) (h2 : term411 A B s f x y) : term269.
Proof. exact (fun h0 : ~ False => @lem5095931 A B g s f x y h1 h2). Qed.
Lemma lem5095934 (p : Prop) : (term217 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5095935 : term269 = False.
Proof. exact (@lem5095934 False). Qed.
Lemma lem5095936 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term23 A B s g f) (h2 : term411 A B s f x y) : False.
Proof. exact (EQ_MP (@lem5095935) (@lem5095932 A B g s f x y h1 h2)). Qed.
Lemma lem5096045 {A : Type'} (s : A -> Prop) (n : nat) (h1 : @HAS_SIZE A s n) : @HAS_SIZE A s n.
Proof. exact (h1). Qed.
Lemma lem5096046 {A : Type'} (s : A -> Prop) (n : nat) (h1 : @HAS_SIZE A s n) : term452 A s n.
Proof. exact (fun h0 : term350 A s n => @lem5096045 A s n h1). Qed.
Lemma lem5096048 (p : Prop) : (term217 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5096049 {A : Type'} (s : A -> Prop) (n : nat) : (term452 A s n) = (@HAS_SIZE A s n).
Proof. exact (@lem5096048 (@HAS_SIZE A s n)). Qed.
Lemma lem5096050 {A : Type'} (s : A -> Prop) (n : nat) (h1 : @HAS_SIZE A s n) : @HAS_SIZE A s n.
Proof. exact (EQ_MP (@lem5096049 A s n) (@lem5096046 A s n h1)). Qed.
Lemma lem5096053 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5096055 {A : Type'} (s : A -> Prop) (n : nat) : (term350 A s n) = (term453 A s n).
Proof. exact (@lem5096053 (@HAS_SIZE A s n)). Qed.
Lemma lem5096058 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term350 A s n) : term453 A s n.
Proof. exact (EQ_MP (@lem5096055 A s n) (@lem5095500 A s n h1)). Qed.
Lemma lem5096061 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term350 A s n) (h2 : @HAS_SIZE A s n) : False.
Proof. exact (@lem5096058 A s n h1 (@lem5096050 A s n h2)). Qed.
Lemma lem5096062 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term350 A s n) (h2 : @HAS_SIZE A s n) : term269.
Proof. exact (fun h0 : ~ False => @lem5096061 A s n h1 h2). Qed.
Lemma lem5096064 (p : Prop) : (term217 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5096065 : term269 = False.
Proof. exact (@lem5096064 False). Qed.
Lemma lem5096066 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term350 A s n) (h2 : @HAS_SIZE A s n) : False.
Proof. exact (EQ_MP (@lem5096065) (@lem5096062 A s n h1 h2)). Qed.
Lemma lem5096067 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term350 A s n) (h2 : @HAS_SIZE A s n) : (term350 A s n) = False.
Proof. exact (prop_ext (fun h3 : term350 A s n => @lem5096066 A s n h1 h2) (fun h3 : False => @lem5095500 A s n h1)). Qed.
Lemma lem5096068 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term350 A s n) (h2 : @HAS_SIZE A s n) : False.
Proof. exact (EQ_MP (@lem5096067 A s n h1 h2) (@lem5095500 A s n h1)). Qed.
Lemma lem5096069 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term350 A s n) (h2 : @HAS_SIZE A s n) : (@HAS_SIZE A s n) = False.
Proof. exact (prop_ext (fun h3 : @HAS_SIZE A s n => @lem5096068 A s n h1 h2) (fun h3 : False => @lem5095498 A s n h2)). Qed.
Lemma lem5096070 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term350 A s n) (h2 : @HAS_SIZE A s n) : False.
Proof. exact (EQ_MP (@lem5096069 A s n h1 h2) (@lem5095498 A s n h2)). Qed.
Lemma lem5096071 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term350 A s n) (h2 : @HAS_SIZE A s n) : (term350 A s n) = False.
Proof. exact (prop_ext (fun h3 : term350 A s n => @lem5096070 A s n h1 h2) (fun h3 : False => @lem5095442 A s n h1)). Qed.
Lemma lem5096072 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term350 A s n) (h2 : @HAS_SIZE A s n) : False.
Proof. exact (EQ_MP (@lem5096071 A s n h1 h2) (@lem5095442 A s n h1)). Qed.
Lemma lem5096073 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term350 A s n) (h2 : @HAS_SIZE A s n) : (@HAS_SIZE A s n) = False.
Proof. exact (prop_ext (fun h3 : @HAS_SIZE A s n => @lem5096072 A s n h1 h2) (fun h3 : False => @lem5095438 A s n h2)). Qed.
Lemma lem5096074 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term350 A s n) (h2 : @HAS_SIZE A s n) : False.
Proof. exact (EQ_MP (@lem5096073 A s n h1 h2) (@lem5095438 A s n h2)). Qed.
Lemma lem5096075 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term350 A s n) (h2 : @HAS_SIZE A s n) : (term350 A s n) = False.
Proof. exact (prop_ext (fun h3 : term350 A s n => @lem5096074 A s n h1 h2) (fun h3 : False => @lem5095442 A s n h1)). Qed.
Lemma lem5096076 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term350 A s n) (h2 : @HAS_SIZE A s n) : False.
Proof. exact (EQ_MP (@lem5096075 A s n h1 h2) (@lem5095442 A s n h1)). Qed.
Lemma lem5096077 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term350 A s n) (h2 : @HAS_SIZE A s n) : (@HAS_SIZE A s n) = False.
Proof. exact (prop_ext (fun h3 : @HAS_SIZE A s n => @lem5096076 A s n h1 h2) (fun h3 : False => @lem5095438 A s n h2)). Qed.
Lemma lem5096078 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term350 A s n) (h2 : @HAS_SIZE A s n) : False.
Proof. exact (EQ_MP (@lem5096077 A s n h1 h2) (@lem5095438 A s n h2)). Qed.
Lemma lem5096079 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) (y : A) (s : A -> Prop) (n : nat) (h1 : term23 A B s g f) (h2 : @HAS_SIZE A s n) (h3 : term383 A B f x y s n) : False.
Proof. exact (or_elim (@lem5095314 A B f x y s n h3) (fun h0 : term411 A B s f x y => @lem5095936 A B g s f x y h1 h0) (fun h0 : term350 A s n => @lem5096078 A s n h0 h2)). Qed.
Lemma lem5096080 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) (y : A) (s : A -> Prop) (n : nat) (h1 : term23 A B s g f) (h2 : @HAS_SIZE A s n) (h3 : term383 A B f x y s n) : (@HAS_SIZE A s n) = False.
Proof. exact (prop_ext (fun h4 : @HAS_SIZE A s n => @lem5096079 A B g f x y s n h1 h2 h3) (fun h4 : False => @lem5095259 A s n h2)). Qed.
Lemma lem5096081 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) (y : A) (s : A -> Prop) (n : nat) (h1 : term23 A B s g f) (h2 : @HAS_SIZE A s n) (h3 : term383 A B f x y s n) : False.
Proof. exact (EQ_MP (@lem5096080 A B g f x y s n h1 h2 h3) (@lem5095259 A s n h2)). Qed.
Lemma lem5096082 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) (s : A -> Prop) (n : nat) (h1 : term23 A B s g f) (h2 : term386 A B f x s n) (h3 : @HAS_SIZE A s n) : False.
Proof. exact (ex_elim (@lem5095165 A B f x s n h2) (fun y : A => fun h0 : term385 A B f x s n y => @lem5096081 A B g f x y s n h1 h3 h0)). Qed.
Lemma lem5096083 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term23 A B s g f) (h2 : term287 A B f s n) (h3 : @HAS_SIZE A s n) : False.
Proof. exact (ex_elim (@lem5095164 A B f s n h2) (fun x : A => fun h0 : term387 A B f s n x => @lem5096082 A B g f x s n h1 h0 h3)). Qed.
Lemma lem5096084 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term23 A B s g f) (h2 : term287 A B f s n) (h3 : @HAS_SIZE A s n) : (@HAS_SIZE A s n) = False.
Proof. exact (prop_ext (fun h4 : @HAS_SIZE A s n => @lem5096083 A B g f s n h1 h2 h3) (fun h4 : False => @lem5095015 A s n h3)). Qed.
Lemma lem5096085 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term23 A B s g f) (h2 : term287 A B f s n) (h3 : @HAS_SIZE A s n) : False.
Proof. exact (EQ_MP (@lem5096084 A B g f s n h1 h2 h3) (@lem5095015 A s n h3)). Qed.
Lemma lem5096086 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term23 A B s g f) (h2 : term287 A B f s n) (h3 : @HAS_SIZE A s n) : (term287 A B f s n) = False.
Proof. exact (prop_ext (fun h4 : term287 A B f s n => @lem5096085 A B g f s n h1 h2 h3) (fun h4 : False => @lem5094875 A B f s n h2)). Qed.
Lemma lem5096087 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term23 A B s g f) (h2 : term287 A B f s n) (h3 : @HAS_SIZE A s n) : False.
Proof. exact (EQ_MP (@lem5096086 A B g f s n h1 h2 h3) (@lem5094875 A B f s n h2)). Qed.
Lemma lem5096088 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term23 A B s g f) (h2 : @HAS_SIZE A s n) : term286 A B f s n.
Proof. exact (fun h0 : term287 A B f s n => @lem5096087 A B g f s n h1 h0 h2). Qed.
Lemma lem5096089 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term23 A B s g f) (h2 : @HAS_SIZE A s n) : term7 A B f s n.
Proof. exact (EQ_MP (@lem5094874 A B f s n) (@lem5096088 A B g f s n h1 h2)). Qed.
Lemma lem5096090 {A B : Type'} (n : nat) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term23 A B s g f) : term295 A B f s n.
Proof. exact (fun h0 : @HAS_SIZE A s n => @lem5096089 A B g f s n h1 h0). Qed.
Lemma lem5096091 {A B : Type'} (n : nat) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term23 A B s g f) : term298 A B g f s n.
Proof. exact (fun h0 : term29 A B s f g => @lem5096090 A B n s g f h1). Qed.
Lemma lem5096092 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (n : nat) : term300 A B g f s n.
Proof. exact (fun h0 : term23 A B s g f => @lem5096091 A B n s g f h0). Qed.
Lemma lem5096097 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : term304 A B f s n.
Proof. exact (fun g : B -> A => @lem5096092 A B g f s n). Qed.
Lemma lem5096102 {A B : Type'} (s : A -> Prop) (n : nat) : term308 A B s n.
Proof. exact (fun f : A -> B => @lem5096097 A B f s n). Qed.
Lemma lem5096107 {A B : Type'} (n : nat) : term312 A B n.
Proof. exact (fun s : A -> Prop => @lem5096102 A B s n). Qed.
Lemma lem5096112 {A B : Type'} : term316 A B.
Proof. exact (fun n : nat => @lem5096107 A B n). Qed.
Lemma lem5096113 {A B : Type'} : term315 A B.
Proof. exact (EQ_MP (@lem5094867 A B) (@lem5096112 A B)). Qed.
Lemma lem5096114 {A B : Type'} (n : nat) : term454 A B n.
Proof. exact (@lem5096113 A B n). Qed.
Lemma lem5096115 {A B : Type'} (n : nat) : (term454 A B n) = (term311 A B n).
Proof. exact (eq_refl (term454 A B n)). Qed.
Lemma lem5096116 {A B : Type'} (n : nat) : term311 A B n.
Proof. exact (EQ_MP (@lem5096115 A B n) (@lem5096114 A B n)). Qed.
Lemma lem5096117 {A B : Type'} (n : nat) (s : A -> Prop) : term455 A B n s.
Proof. exact (@lem5096116 A B n s). Qed.
Lemma lem5096118 {A B : Type'} (s : A -> Prop) (n : nat) : (term455 A B n s) = (term307 A B s n).
Proof. exact (eq_refl (term455 A B n s)). Qed.
Lemma lem5096119 {A B : Type'} (s : A -> Prop) (n : nat) : term307 A B s n.
Proof. exact (EQ_MP (@lem5096118 A B s n) (@lem5096117 A B n s)). Qed.
Lemma lem5096120 {A B : Type'} (s : A -> Prop) (n : nat) (f : A -> B) : term456 A B s n f.
Proof. exact (@lem5096119 A B s n f). Qed.
Lemma lem5096121 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term456 A B s n f) = (term303 A B f s n).
Proof. exact (eq_refl (term456 A B s n f)). Qed.
Lemma lem5096122 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : term303 A B f s n.
Proof. exact (EQ_MP (@lem5096121 A B f s n) (@lem5096120 A B s n f)). Qed.
Lemma lem5096123 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (g : B -> A) : term457 A B f s n g.
Proof. exact (@lem5096122 A B f s n g). Qed.
Lemma lem5096124 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (n : nat) : (term457 A B f s n g) = (term288 A B g f s n).
Proof. exact (eq_refl (term457 A B f s n g)). Qed.
Lemma lem5096125 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (n : nat) : term288 A B g f s n.
Proof. exact (EQ_MP (@lem5096124 A B g f s n) (@lem5096123 A B f s n g)). Qed.
Lemma lem5096127 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (n : nat) : term288 A B g f s n.
Proof. exact (@lem5094619 A B g f s n (@lem5096125 A B g f s n)). Qed.
Lemma lem5096128 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term13 A B s t g f) (h2 : t = (@IMAGE A B f s)) : term297 A B g f s n.
Proof. exact (@lem5096127 A B g f s n (@lem5092724 A B g t f s h1 h2)). Qed.
Lemma lem5096129 {A B : Type'} (n : nat) (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term13 A B s t g f) (h2 : term14 A B t s f g) (h3 : t = (@IMAGE A B f s)) : term294 A B f s n.
Proof. exact (@lem5096128 A B n g t f s h1 h3 (@lem5092737 A B g t f s h2 h3)). Qed.
Lemma lem5096130 {A B : Type'} (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term13 A B s t g f) (h2 : term14 A B t s f g) (h3 : t = (@IMAGE A B f s)) (h4 : @HAS_SIZE A s n) : term286 A B f s n.
Proof. exact (@lem5096129 A B n g t f s h1 h2 h3 (@lem5092751 A s n h4)). Qed.
Lemma lem5096131 {A B : Type'} (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term13 A B s t g f) (h2 : term14 A B t s f g) (h3 : term287 A B f s n) (h4 : t = (@IMAGE A B f s)) (h5 : @HAS_SIZE A s n) : False.
Proof. exact (@lem5096130 A B g t f s n h1 h2 h4 h5 (@lem5094603 A B f s n h3)). Qed.
Lemma lem5096132 {A B : Type'} (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term13 A B s t g f) (h2 : term14 A B t s f g) (h3 : term287 A B f s n) (h4 : t = (@IMAGE A B f s)) (h5 : @HAS_SIZE A s n) : (term287 A B f s n) = False.
Proof. exact (prop_ext (fun h6 : term287 A B f s n => @lem5096131 A B g t f s n h1 h2 h3 h4 h5) (fun h6 : False => @lem5094603 A B f s n h3)). Qed.
Lemma lem5096133 {A B : Type'} (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term13 A B s t g f) (h2 : term14 A B t s f g) (h3 : term287 A B f s n) (h4 : t = (@IMAGE A B f s)) (h5 : @HAS_SIZE A s n) : False.
Proof. exact (EQ_MP (@lem5096132 A B g t f s n h1 h2 h3 h4 h5) (@lem5094603 A B f s n h3)). Qed.
Lemma lem5096134 {A B : Type'} (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term13 A B s t g f) (h2 : term14 A B t s f g) (h3 : t = (@IMAGE A B f s)) (h4 : @HAS_SIZE A s n) : term286 A B f s n.
Proof. exact (fun h0 : term287 A B f s n => @lem5096133 A B g t f s n h1 h2 h0 h3 h4). Qed.
Lemma lem5096135 {A B : Type'} (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term13 A B s t g f) (h2 : term14 A B t s f g) (h3 : t = (@IMAGE A B f s)) (h4 : @HAS_SIZE A s n) : term7 A B f s n.
Proof. exact (EQ_MP (@lem5094602 A B f s n) (@lem5096134 A B g t f s n h1 h2 h3 h4)). Qed.
Lemma lem5096136 {A B : Type'} (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term13 A B s t g f) (h2 : term14 A B t s f g) (h3 : t = (@IMAGE A B f s)) (h4 : @HAS_SIZE A s n) : term8 A B f s n.
Proof. exact (@lem5094598 A B f s n (@lem5096135 A B g t f s n h1 h2 h3 h4)). Qed.
Lemma lem5096137 {A B : Type'} (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term13 A B s t g f) (h2 : term14 A B t s f g) (h3 : t = (@IMAGE A B f s)) (h4 : @HAS_SIZE A s n) : (@HAS_SIZE A s n) = (term8 A B f s n).
Proof. exact (prop_ext (fun h5 : @HAS_SIZE A s n => @lem5096136 A B g t f s n h1 h2 h3 h4) (fun h5 : term8 A B f s n => @lem5092751 A s n h4)). Qed.
Lemma lem5096138 {A B : Type'} (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term13 A B s t g f) (h2 : term14 A B t s f g) (h3 : t = (@IMAGE A B f s)) (h4 : @HAS_SIZE A s n) : term8 A B f s n.
Proof. exact (EQ_MP (@lem5096137 A B g t f s n h1 h2 h3 h4) (@lem5092751 A s n h4)). Qed.
Lemma lem5096139 {A B : Type'} (g : B -> A) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term13 A B s t g f) (h2 : term14 A B t s f g) (h3 : t = (@IMAGE A B f s)) (h4 : @HAS_SIZE A s n) : @HAS_SIZE B t n.
Proof. exact (EQ_MP (@lem5092711 A B n t f s h3) (@lem5096138 A B g t f s n h1 h2 h3 h4)). Qed.
Lemma lem5096140 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (s : A -> Prop) (n : nat) (h1 : term13 A B s t g f) (h2 : term14 A B t s f g) (h3 : @HAS_SIZE A s n) : (t = (@IMAGE A B f s)) = (@HAS_SIZE B t n).
Proof. exact (prop_ext (fun h4 : t = (@IMAGE A B f s) => @lem5096139 A B g t f s n h1 h2 h4 h3) (fun h4 : @HAS_SIZE B t n => @lem5094595 A B t f g s n h1 h2 h3)). Qed.
Lemma lem5096141 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (s : A -> Prop) (n : nat) (h1 : term13 A B s t g f) (h2 : term14 A B t s f g) (h3 : @HAS_SIZE A s n) : @HAS_SIZE B t n.
Proof. exact (EQ_MP (@lem5096140 A B t f g s n h1 h2 h3) (@lem5094595 A B t f g s n h1 h2 h3)). Qed.
Lemma lem5096142 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (s : A -> Prop) (n : nat) (h1 : term11 A B t f g s n) : term12 A B t f g s n.
Proof. exact (proj2 (@lem5092693 A B t f g s n h1)). Qed.
Lemma lem5096143 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (s : A -> Prop) (n : nat) (h1 : term11 A B t f g s n) : term13 A B s t g f.
Proof. exact (proj1 (@lem5092693 A B t f g s n h1)). Qed.
Lemma lem5096144 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (s : A -> Prop) (n : nat) (h1 : term12 A B t f g s n) : @HAS_SIZE A s n.
Proof. exact (proj2 (@lem5092694 A B t f g s n h1)). Qed.
Lemma lem5096145 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (s : A -> Prop) (n : nat) (h1 : term12 A B t f g s n) : term14 A B t s f g.
Proof. exact (proj1 (@lem5092694 A B t f g s n h1)). Qed.
Lemma lem5096146 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (s : A -> Prop) (n : nat) (h1 : term13 A B s t g f) (h2 : term14 A B t s f g) (h3 : @HAS_SIZE A s n) : (@HAS_SIZE A s n) = (@HAS_SIZE B t n).
Proof. exact (prop_ext (fun h4 : @HAS_SIZE A s n => @lem5096141 A B t f g s n h1 h2 h3) (fun h4 : @HAS_SIZE B t n => @lem5092696 A s n h3)). Qed.
Lemma lem5096147 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (s : A -> Prop) (n : nat) (h1 : term13 A B s t g f) (h2 : term14 A B t s f g) (h3 : @HAS_SIZE A s n) : @HAS_SIZE B t n.
Proof. exact (EQ_MP (@lem5096146 A B t f g s n h1 h2 h3) (@lem5092696 A s n h3)). Qed.
Lemma lem5096148 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (s : A -> Prop) (n : nat) (h1 : term13 A B s t g f) (h2 : term14 A B t s f g) (h3 : @HAS_SIZE A s n) : (term14 A B t s f g) = (@HAS_SIZE B t n).
Proof. exact (prop_ext (fun h4 : term14 A B t s f g => @lem5096147 A B t f g s n h1 h2 h3) (fun h4 : @HAS_SIZE B t n => @lem5092697 A B t s f g h2)). Qed.
Lemma lem5096149 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (s : A -> Prop) (n : nat) (h1 : term13 A B s t g f) (h2 : term14 A B t s f g) (h3 : @HAS_SIZE A s n) : @HAS_SIZE B t n.
Proof. exact (EQ_MP (@lem5096148 A B t f g s n h1 h2 h3) (@lem5092697 A B t s f g h2)). Qed.
Lemma lem5096150 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (s : A -> Prop) (n : nat) (h1 : term13 A B s t g f) (h2 : term14 A B t s f g) (h3 : term12 A B t f g s n) : (@HAS_SIZE A s n) = (@HAS_SIZE B t n).
Proof. exact (prop_ext (fun h4 : @HAS_SIZE A s n => @lem5096149 A B t f g s n h1 h2 h4) (fun h4 : @HAS_SIZE B t n => @lem5096144 A B t f g s n h3)). Qed.
Lemma lem5096151 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (s : A -> Prop) (n : nat) (h1 : term13 A B s t g f) (h2 : term14 A B t s f g) (h3 : term12 A B t f g s n) : @HAS_SIZE B t n.
Proof. exact (EQ_MP (@lem5096150 A B t f g s n h1 h2 h3) (@lem5096144 A B t f g s n h3)). Qed.
Lemma lem5096152 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (s : A -> Prop) (n : nat) (h1 : term13 A B s t g f) (h2 : term12 A B t f g s n) : (term14 A B t s f g) = (@HAS_SIZE B t n).
Proof. exact (prop_ext (fun h3 : term14 A B t s f g => @lem5096151 A B t f g s n h1 h3 h2) (fun h3 : @HAS_SIZE B t n => @lem5096145 A B t f g s n h2)). Qed.
Lemma lem5096153 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (s : A -> Prop) (n : nat) (h1 : term13 A B s t g f) (h2 : term12 A B t f g s n) : @HAS_SIZE B t n.
Proof. exact (EQ_MP (@lem5096152 A B t f g s n h1 h2) (@lem5096145 A B t f g s n h2)). Qed.
Lemma lem5096154 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (s : A -> Prop) (n : nat) (h1 : term13 A B s t g f) (h2 : term12 A B t f g s n) : (term13 A B s t g f) = (@HAS_SIZE B t n).
Proof. exact (prop_ext (fun h3 : term13 A B s t g f => @lem5096153 A B t f g s n h1 h2) (fun h3 : @HAS_SIZE B t n => @lem5092695 A B s t g f h1)). Qed.
Lemma lem5096155 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (s : A -> Prop) (n : nat) (h1 : term13 A B s t g f) (h2 : term12 A B t f g s n) : @HAS_SIZE B t n.
Proof. exact (EQ_MP (@lem5096154 A B t f g s n h1 h2) (@lem5092695 A B s t g f h1)). Qed.
Lemma lem5096156 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (s : A -> Prop) (n : nat) (h1 : term13 A B s t g f) (h2 : term11 A B t f g s n) : (term12 A B t f g s n) = (@HAS_SIZE B t n).
Proof. exact (prop_ext (fun h3 : term12 A B t f g s n => @lem5096155 A B t f g s n h1 h3) (fun h3 : @HAS_SIZE B t n => @lem5096142 A B t f g s n h2)). Qed.
Lemma lem5096157 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (s : A -> Prop) (n : nat) (h1 : term13 A B s t g f) (h2 : term11 A B t f g s n) : @HAS_SIZE B t n.
Proof. exact (EQ_MP (@lem5096156 A B t f g s n h1 h2) (@lem5096142 A B t f g s n h2)). Qed.
Lemma lem5096158 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (s : A -> Prop) (n : nat) (h1 : term11 A B t f g s n) : (term13 A B s t g f) = (@HAS_SIZE B t n).
Proof. exact (prop_ext (fun h2 : term13 A B s t g f => @lem5096157 A B t f g s n h2 h1) (fun h2 : @HAS_SIZE B t n => @lem5096143 A B t f g s n h1)). Qed.
Lemma lem5096159 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (s : A -> Prop) (n : nat) (h1 : term11 A B t f g s n) : @HAS_SIZE B t n.
Proof. exact (EQ_MP (@lem5096158 A B t f g s n h1) (@lem5096143 A B t f g s n h1)). Qed.
Lemma lem5096160 {A B : Type'} (f : A -> B) (g : B -> A) (s : A -> Prop) (t : B -> Prop) (n : nat) : term458 A B f g s t n.
Proof. exact (fun h0 : term11 A B t f g s n => @lem5096159 A B t f g s n h0). Qed.
Lemma lem5096165 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (n : nat) : term459 A B f s t n.
Proof. exact (fun g : B -> A => @lem5096160 A B f g s t n). Qed.
Lemma lem5096170 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (n : nat) : term460 A B s t n.
Proof. exact (fun f : A -> B => @lem5096165 A B f s t n). Qed.
Lemma lem5096175 {A B : Type'} (s : A -> Prop) (n : nat) : term461 A B s n.
Proof. exact (fun t : B -> Prop => @lem5096170 A B s t n). Qed.
Lemma lem5096180 {A B : Type'} (n : nat) : term462 A B n.
Proof. exact (fun s : A -> Prop => @lem5096175 A B s n). Qed.
