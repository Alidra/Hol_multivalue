Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_EQ_GENERAL_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EQ_TRANS_spec.
Require Import EXTENSION_spec.
Require Import IN_IMAGE_spec.
Require Import ITERATE_EQ_spec.
Require Import ITERATE_IMAGE_spec.
Require Import o_THM_spec.
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
Require Import thm18897_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18940_spec.
Require Import thm18941_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
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
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem5986610 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5986611 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5986612 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5986611 t1) (@lem5986610 t1)). Qed.
Lemma lem5986613 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5986612 t1 t2). Qed.
Lemma lem5986614 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5986615 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5986614 t1 t2) (@lem5986613 t1 t2)). Qed.
Lemma lem5986616 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5986615 t1 t2 t3). Qed.
Lemma lem5986617 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5986618 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5986617 t1 t2 t3) (@lem5986616 t1 t2 t3)). Qed.
Lemma lem5986619 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5986618 t1 t2 t3)). Qed.
Lemma lem5986620 {A B C : Type'} (op : type1400 C) : term7 A B C op.
Proof. exact (@lem5942955 A B C op). Qed.
Lemma lem5986621 {A B C : Type'} (op : type1400 C) : (term7 A B C op) = (term8 A B C op).
Proof. exact (eq_refl (term7 A B C op)). Qed.
Lemma lem5986633 {A : Type'} (h1 : term9 A) : term9 A.
Proof. exact (h1). Qed.
Lemma lem5986634 {A : Type'} (x : A) (h1 : term9 A) : term10 A x.
Proof. exact (@lem5986633 A h1 x). Qed.
Lemma lem5986635 {A : Type'} (x : A) : (term10 A x) = (term11 A x).
Proof. exact (eq_refl (term10 A x)). Qed.
Lemma lem5986636 {A : Type'} (x : A) (h1 : term9 A) : term11 A x.
Proof. exact (EQ_MP (@lem5986635 A x) (@lem5986634 A x h1)). Qed.
Lemma lem5986637 {A : Type'} (x : A) (y : A) (h1 : term9 A) : term12 A x y.
Proof. exact (@lem5986636 A x h1 y). Qed.
Lemma lem5986638 {A : Type'} (y : A) (x : A) : (term12 A x y) = (term13 A y x).
Proof. exact (eq_refl (term12 A x y)). Qed.
Lemma lem5986639 {A : Type'} (y : A) (x : A) (h1 : term9 A) : term13 A y x.
Proof. exact (EQ_MP (@lem5986638 A y x) (@lem5986637 A x y h1)). Qed.
Lemma lem5986640 {A : Type'} (y : A) (x : A) (z : A) (h1 : term9 A) : term14 A y x z.
Proof. exact (@lem5986639 A y x h1 z). Qed.
Lemma lem5986641 {A : Type'} (y : A) (x : A) (z : A) : (term14 A y x z) = (term15 A y x z).
Proof. exact (eq_refl (term14 A y x z)). Qed.
Lemma lem5986642 {A : Type'} (y : A) (x : A) (z : A) (h1 : term9 A) : term15 A y x z.
Proof. exact (EQ_MP (@lem5986641 A y x z) (@lem5986640 A y x z h1)). Qed.
Lemma lem5986643 {A : Type'} (x : A) (y : A) (z : A) (h1 : term16 A x y z) : term16 A x y z.
Proof. exact (h1). Qed.
Lemma lem5986644 {A : Type'} (x : A) (y : A) (z : A) (h1 : term9 A) (h2 : term16 A x y z) : x = z.
Proof. exact (@lem5986642 A y x z h1 (@lem5986643 A x y z h2)). Qed.
Lemma lem5986645 {A : Type'} (x : A) (y : A) (z : A) (h1 : term16 A x y z) : term17 A x z.
Proof. exact (fun h0 : term9 A => @lem5986644 A x y z h0 h1). Qed.
Lemma lem5986646 {A : Type'} (x : A) (z : A) (h1 : term18 A x z) : term18 A x z.
Proof. exact (h1). Qed.
Lemma lem5986647 {A : Type'} (x : A) (z : A) (h1 : term18 A x z) : term17 A x z.
Proof. exact (ex_elim (@lem5986646 A x z h1) (fun y : A => fun h0 : term19 A x z y => @lem5986645 A x y z h0)). Qed.
Lemma lem5986648 {A : Type'} (h1 : term9 A) : term9 A.
Proof. exact (h1). Qed.
Lemma lem5986649 {A : Type'} (x : A) (z : A) (h1 : term9 A) (h2 : term18 A x z) : x = z.
Proof. exact (@lem5986647 A x z h2 (@lem5986648 A h1)). Qed.
Lemma lem5986650 {A : Type'} (x : A) (z : A) (h1 : term9 A) : term20 A x z.
Proof. exact (fun h0 : term18 A x z => @lem5986649 A x z h1 h0). Qed.
Lemma lem5986651 {A : Type'} (x : A) (h1 : term9 A) : term21 A x.
Proof. exact (fun z : A => @lem5986650 A x z h1). Qed.
Lemma lem5986652 {A : Type'} (h1 : term9 A) : term22 A.
Proof. exact (fun x : A => @lem5986651 A x h1). Qed.
Lemma lem5986653 {A : Type'} : term23 A.
Proof. exact (fun h0 : term9 A => @lem5986652 A h0). Qed.
Lemma lem5986654 {A : Type'} : term22 A.
Proof. exact (@lem5986653 A (@lem403 A)). Qed.
Lemma lem5986655 {A : Type'} (x : A) : term24 A x.
Proof. exact (@lem5986654 A x). Qed.
Lemma lem5986656 {A : Type'} (x : A) : (term24 A x) = (term21 A x).
Proof. exact (eq_refl (term24 A x)). Qed.
Lemma lem5986657 {A : Type'} (x : A) : term21 A x.
Proof. exact (EQ_MP (@lem5986656 A x) (@lem5986655 A x)). Qed.
Lemma lem5986658 {A : Type'} (x : A) (z : A) : term25 A x z.
Proof. exact (@lem5986657 A x z). Qed.
Lemma lem5986659 {A : Type'} (x : A) (z : A) : (term25 A x z) = (term20 A x z).
Proof. exact (eq_refl (term25 A x z)). Qed.
Lemma lem5986671 {A B : Type'} (y : B) : term26 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem5986672 {A B : Type'} (y : B) : (term26 A B y) = (term27 A B y).
Proof. exact (eq_refl (term26 A B y)). Qed.
Lemma lem5986673 {A B : Type'} (y : B) : term27 A B y.
Proof. exact (EQ_MP (@lem5986672 A B y) (@lem5986671 A B y)). Qed.
Lemma lem5986674 {A B : Type'} (y : B) (s : A -> Prop) : term28 A B y s.
Proof. exact (@lem5986673 A B y s). Qed.
Lemma lem5986675 {A B : Type'} (y : B) (s : A -> Prop) : (term28 A B y s) = (term29 A B y s).
Proof. exact (eq_refl (term28 A B y s)). Qed.
Lemma lem5986676 {A B : Type'} (y : B) (s : A -> Prop) : term29 A B y s.
Proof. exact (EQ_MP (@lem5986675 A B y s) (@lem5986674 A B y s)). Qed.
Lemma lem5986677 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term30 A B y s f.
Proof. exact (@lem5986676 A B y s f). Qed.
Lemma lem5986678 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term30 A B y s f) = ((term31 A B y f s) = (term32 A B y f s)).
Proof. exact (eq_refl (term30 A B y s f)). Qed.
Lemma lem5986680 {A : Type'} (s : A -> Prop) : term33 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem5986681 {A : Type'} (s : A -> Prop) : (term33 A s) = (term34 A s).
Proof. exact (eq_refl (term33 A s)). Qed.
Lemma lem5986682 {A : Type'} (s : A -> Prop) : term34 A s.
Proof. exact (EQ_MP (@lem5986681 A s) (@lem5986680 A s)). Qed.
Lemma lem5986683 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term35 A s t.
Proof. exact (@lem5986682 A s t). Qed.
Lemma lem5986684 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term35 A s t) = ((s = t) = (term36 A s t)).
Proof. exact (eq_refl (term35 A s t)). Qed.
Lemma lem5986686 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (h1). Qed.
Lemma lem5986687 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term37 A B C s t g h f) : term37 A B C s t g h f.
Proof. exact (h1). Qed.
Lemma lem5986688 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term38 A B C s t g h f.
Proof. exact (h1). Qed.
Lemma lem5986689 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (h1 : term39 A B t s h) : term39 A B t s h.
Proof. exact (h1). Qed.
Lemma lem5986690 {A B : Type'} (t : B -> Prop) (h : A -> B) (s : A -> Prop) (h1 : t = (@IMAGE A B h s)) : t = (@IMAGE A B h s).
Proof. exact (h1). Qed.
Lemma lem5986691 {A B C : Type'} (s : A -> Prop) (f : A -> C) (op : type1400 C) (g : B -> C) : (term40 A B C s f op g) = (term40 A B C s f op g).
Proof. exact (eq_refl (term40 A B C s f op g)). Qed.
Lemma lem5986692 {A B C : Type'} (f : A -> C) (op : type1400 C) (g : B -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) (h1 : t = (@IMAGE A B h s)) : (term41 A B C s f op g t) = (term42 A B C f op g h s).
Proof. exact (MK_COMB (@lem5986691 A B C s f op g) (@lem5986690 A B t h s h1)). Qed.
Lemma lem5986693 {A B C : Type'} (f : A -> C) (op : type1400 C) (h : A -> B) (s : A -> Prop) (g : B -> C) : (term42 A B C f op g h s) = ((@iterate C A op s f) = (term43 A B C op h s g)).
Proof. exact (eq_refl (term42 A B C f op g h s)). Qed.
Lemma lem5986694 {A B C : Type'} (s : A -> Prop) (f : A -> C) (op : type1400 C) (g : B -> C) (t : B -> Prop) : (term44 A B C s f op g t) = (term44 A B C s f op g t).
Proof. exact (eq_refl (term44 A B C s f op g t)). Qed.
Lemma lem5986695 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (h : A -> B) (s : A -> Prop) (g : B -> C) : ((term41 A B C s f op g t) = (term42 A B C f op g h s)) = ((term41 A B C s f op g t) = ((@iterate C A op s f) = (term43 A B C op h s g))).
Proof. exact (MK_COMB (@lem5986694 A B C s f op g t) (@lem5986693 A B C f op h s g)). Qed.
Lemma lem5986696 {A B C : Type'} (s : A -> Prop) (f : A -> C) (op : type1400 C) (t : B -> Prop) (g : B -> C) : (term41 A B C s f op g t) = ((@iterate C A op s f) = (@iterate C B op t g)).
Proof. exact (eq_refl (term41 A B C s f op g t)). Qed.
Lemma lem5986697 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5986698 {A B C : Type'} (s : A -> Prop) (f : A -> C) (op : type1400 C) (t : B -> Prop) (g : B -> C) : (term44 A B C s f op g t) = (term45 A B C s f op t g).
Proof. exact (MK_COMB (@lem5986697) (@lem5986696 A B C s f op t g)). Qed.
Lemma lem5986699 {A B C : Type'} (f : A -> C) (op : type1400 C) (h : A -> B) (s : A -> Prop) (g : B -> C) : ((@iterate C A op s f) = (term43 A B C op h s g)) = ((@iterate C A op s f) = (term43 A B C op h s g)).
Proof. exact (eq_refl ((@iterate C A op s f) = (term43 A B C op h s g))). Qed.
Lemma lem5986700 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (h : A -> B) (s : A -> Prop) (g : B -> C) : ((term41 A B C s f op g t) = ((@iterate C A op s f) = (term43 A B C op h s g))) = (((@iterate C A op s f) = (@iterate C B op t g)) = ((@iterate C A op s f) = (term43 A B C op h s g))).
Proof. exact (MK_COMB (@lem5986698 A B C s f op t g) (@lem5986699 A B C f op h s g)). Qed.
Lemma lem5986701 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (h : A -> B) (s : A -> Prop) (g : B -> C) : ((term41 A B C s f op g t) = (term42 A B C f op g h s)) = (((@iterate C A op s f) = (@iterate C B op t g)) = ((@iterate C A op s f) = (term43 A B C op h s g))).
Proof. exact (TRANS (@lem5986695 A B C t f op h s g) (@lem5986700 A B C t f op h s g)). Qed.
Lemma lem5986702 {A B C : Type'} (f : A -> C) (op : type1400 C) (g : B -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) (h1 : t = (@IMAGE A B h s)) : ((@iterate C A op s f) = (@iterate C B op t g)) = ((@iterate C A op s f) = (term43 A B C op h s g)).
Proof. exact (EQ_MP (@lem5986701 A B C t f op h s g) (@lem5986692 A B C f op g t h s h1)). Qed.
Lemma lem5986703 {A B C : Type'} (f : A -> C) (op : type1400 C) (g : B -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) (h1 : t = (@IMAGE A B h s)) : ((@iterate C A op s f) = (term43 A B C op h s g)) = ((@iterate C A op s f) = (@iterate C B op t g)).
Proof. exact (SYM (@lem5986702 A B C f op g t h s h1)). Qed.
Lemma lem5986707 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term36 A s t).
Proof. exact (EQ_MP (@lem5986684 A s t) (@lem5986683 A s t)). Qed.
Lemma lem5986708 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term36 B s t).
Proof. exact (@lem5986707 B s t). Qed.
Lemma lem5986709 {A B : Type'} (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (t = (@IMAGE A B h s)) = (term46 A B t h s).
Proof. exact (@lem5986708 B t (@IMAGE A B h s)). Qed.
Lemma lem5986719 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term31 A B y f s) = (term32 A B y f s).
Proof. exact (EQ_MP (@lem5986678 A B y f s) (@lem5986677 A B y s f)). Qed.
Lemma lem5986720 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term31 A B y f s) = (term32 A B y f s).
Proof. exact (@lem5986719 A B y f s). Qed.
Lemma lem5986721 {A B : Type'} (x : B) (h : A -> B) (s : A -> Prop) : (term31 A B x h s) = (term32 A B x h s).
Proof. exact (@lem5986720 A B x h s). Qed.
Lemma lem5986732 {B : Type'} (x : B) (t : B -> Prop) : (term47 B x t) = (term47 B x t).
Proof. exact (eq_refl (term47 B x t)). Qed.
Lemma lem5986733 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : ((@IN B x t) = (term31 A B x h s)) = ((@IN B x t) = (term32 A B x h s)).
Proof. exact (MK_COMB (@lem5986732 B x t) (@lem5986721 A B x h s)). Qed.
Lemma lem5986738 {A B : Type'} (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term48 A B t h s) = (term49 A B t h s).
Proof. exact (fun_ext (fun x : B => @lem5986733 A B t x h s)). Qed.
Lemma lem5986739 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5986740 {A B : Type'} (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term46 A B t h s) = (term50 A B t h s).
Proof. exact (MK_COMB (@lem5986739 B) (@lem5986738 A B t h s)). Qed.
Lemma lem5986745 {A B : Type'} (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (t = (@IMAGE A B h s)) = (term50 A B t h s).
Proof. exact (TRANS (@lem5986709 A B t h s) (@lem5986740 A B t h s)). Qed.
Lemma lem5986746 {A B : Type'} (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term50 A B t h s) = (t = (@IMAGE A B h s)).
Proof. exact (SYM (@lem5986745 A B t h s)). Qed.
Lemma lem5986748 (p : Prop) : p = (term51 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5986749 {A B : Type'} (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term50 A B t h s) = (term52 A B t h s).
Proof. exact (@lem5986748 (term50 A B t h s)). Qed.
Lemma lem5986750 {A B : Type'} (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term52 A B t h s) = (term50 A B t h s).
Proof. exact (SYM (@lem5986749 A B t h s)). Qed.
Lemma lem5986751 {A B : Type'} (t : B -> Prop) (h : A -> B) (s : A -> Prop) (h1 : term53 A B t h s) : term53 A B t h s.
Proof. exact (h1). Qed.
Lemma lem5986754 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) (h1 : term54 A B C op g f t h s) : term54 A B C op g f t h s.
Proof. exact (h1). Qed.
Lemma lem5986755 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : term55 A B C op g f t h s.
Proof. exact (fun h0 : term54 A B C op g f t h s => @lem5986754 A B C op g f t h s h0). Qed.
Lemma lem5986756 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) (h1 : term55 A B C op g f t h s) : term55 A B C op g f t h s.
Proof. exact (h1). Qed.
Lemma lem5986757 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) (h1 : term54 A B C op g f t h s) : term54 A B C op g f t h s.
Proof. exact (h1). Qed.
Lemma lem5986758 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) (h1 : term54 A B C op g f t h s) (h2 : term55 A B C op g f t h s) : term54 A B C op g f t h s.
Proof. exact (@lem5986756 A B C op g f t h s h2 (@lem5986757 A B C op g f t h s h1)). Qed.
Lemma lem5986759 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) (h1 : term54 A B C op g f t h s) : term56 A B C op g f t h s.
Proof. exact (fun h0 : term55 A B C op g f t h s => @lem5986758 A B C op g f t h s h1 h0). Qed.
Lemma lem5986760 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) (h1 : term55 A B C op g f t h s) : term55 A B C op g f t h s.
Proof. exact (h1). Qed.
Lemma lem5986761 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) (h1 : term54 A B C op g f t h s) (h2 : term55 A B C op g f t h s) : term54 A B C op g f t h s.
Proof. exact (@lem5986759 A B C op g f t h s h1 (@lem5986760 A B C op g f t h s h2)). Qed.
Lemma lem5986762 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) (h1 : term55 A B C op g f t h s) : term55 A B C op g f t h s.
Proof. exact (fun h0 : term54 A B C op g f t h s => @lem5986761 A B C op g f t h s h0 h1). Qed.
Lemma lem5986763 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : term57 A B C op g f t h s.
Proof. exact (fun h0 : term55 A B C op g f t h s => @lem5986762 A B C op g f t h s h0). Qed.
Lemma lem5986766 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : term55 A B C op g f t h s.
Proof. exact (@lem5986763 A B C op g f t h s (@lem5986755 A B C op g f t h s)). Qed.
Lemma lem5986767 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : term55 A B C op g f t h s.
Proof. exact (@lem5986766 A B C op g f t h s). Qed.
Lemma lem5986815 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5986816 {A B : Type'} (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term52 A B t h s) = (term58 A B t h s).
Proof. exact (@lem5986815 (term53 A B t h s)). Qed.
Lemma lem5986818 (t : Prop) : (term59 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5986819 {A B : Type'} (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term58 A B t h s) = (term50 A B t h s).
Proof. exact (@lem5986818 (term50 A B t h s)). Qed.
Lemma lem5986824 {A B : Type'} (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term52 A B t h s) = (term50 A B t h s).
Proof. exact (TRANS (@lem5986816 A B t h s) (@lem5986819 A B t h s)). Qed.
Lemma lem5986875 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term60 A B C s t g h f) = (term60 A B C s t g h f).
Proof. exact (eq_refl (term60 A B C s t g h f)). Qed.
Lemma lem5986876 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term61 A B C g f t h s) = (term62 A B C g f t h s).
Proof. exact (MK_COMB (@lem5986875 A B C s t g h f) (@lem5986824 A B t h s)). Qed.
Lemma lem5986879 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term63 A B t s h) = (term63 A B t s h).
Proof. exact (eq_refl (term63 A B t s h)). Qed.
Lemma lem5986880 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term64 A B C g f t h s) = (term65 A B C g f t h s).
Proof. exact (MK_COMB (@lem5986879 A B t s h) (@lem5986876 A B C g f t h s)). Qed.
Lemma lem5986883 {C : Type'} (op : type1400 C) : (term66 C op) = (term66 C op).
Proof. exact (eq_refl (term66 C op)). Qed.
Lemma lem5986884 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term54 A B C op g f t h s) = (term67 A B C op g f t h s).
Proof. exact (MK_COMB (@lem5986883 C op) (@lem5986880 A B C g f t h s)). Qed.
Lemma lem5986887 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term68 A B C g f t h s) = (term69 A B C g f t h s).
Proof. exact (fun_ext (fun op : type1400 C => @lem5986884 A B C op g f t h s)). Qed.
Lemma lem5986888 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem5986889 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term70 A B C g f t h s) = (term71 A B C g f t h s).
Proof. exact (MK_COMB (@lem5986888 C) (@lem5986887 A B C g f t h s)). Qed.
Lemma lem5986894 {A B C : Type'} (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term72 A B C f t h s) = (term73 A B C f t h s).
Proof. exact (fun_ext (fun g : B -> C => @lem5986889 A B C g f t h s)). Qed.
Lemma lem5986895 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem5986896 {A B C : Type'} (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term74 A B C f t h s) = (term75 A B C f t h s).
Proof. exact (MK_COMB (@lem5986895 B C) (@lem5986894 A B C f t h s)). Qed.
Lemma lem5986901 {A B C : Type'} (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term76 A B C t h s) = (term77 A B C t h s).
Proof. exact (fun_ext (fun f : A -> C => @lem5986896 A B C f t h s)). Qed.
Lemma lem5986902 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem5986903 {A B C : Type'} (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term78 A B C t h s) = (term79 A B C t h s).
Proof. exact (MK_COMB (@lem5986902 A C) (@lem5986901 A B C t h s)). Qed.
Lemma lem5986908 {A B C : Type'} (h : A -> B) (s : A -> Prop) : (term80 A B C h s) = (term81 A B C h s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5986903 A B C t h s)). Qed.
Lemma lem5986909 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5986910 {A B C : Type'} (h : A -> B) (s : A -> Prop) : (term82 A B C h s) = (term83 A B C h s).
Proof. exact (MK_COMB (@lem5986909 B) (@lem5986908 A B C h s)). Qed.
Lemma lem5986915 {A B C : Type'} (s : A -> Prop) : (term84 A B C s) = (term85 A B C s).
Proof. exact (fun_ext (fun h : A -> B => @lem5986910 A B C h s)). Qed.
Lemma lem5986916 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5986917 {A B C : Type'} (s : A -> Prop) : (term86 A B C s) = (term87 A B C s).
Proof. exact (MK_COMB (@lem5986916 A B) (@lem5986915 A B C s)). Qed.
Lemma lem5986922 {A B C : Type'} : (term88 A B C) = (term89 A B C).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5986917 A B C s)). Qed.
Lemma lem5986923 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5986932 {A B C : Type'} : (term90 A B C) = (term91 A B C).
Proof. exact (MK_COMB (@lem5986923 A) (@lem5986922 A B C)). Qed.
Lemma lem5986937 {A B : Type'} (x : B) (h : A -> B) (x' : A) (s : A -> Prop) : (term92 A B x h x' s) = (term92 A B x h x' s).
Proof. exact (eq_refl (term92 A B x h x' s)). Qed.
Lemma lem5986938 {A B : Type'} (x : B) (h : A -> B) (s : A -> Prop) : (term93 A B x h s) = (term93 A B x h s).
Proof. exact (fun_ext (fun x' : A => @lem5986937 A B x h x' s)). Qed.
Lemma lem5986939 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5986940 {A B : Type'} (x : B) (h : A -> B) (s : A -> Prop) : (term32 A B x h s) = (term32 A B x h s).
Proof. exact (MK_COMB (@lem5986939 A) (@lem5986938 A B x h s)). Qed.
Lemma lem5986943 {B : Type'} (x : B) (t : B -> Prop) : (term47 B x t) = (term47 B x t).
Proof. exact (eq_refl (term47 B x t)). Qed.
Lemma lem5986944 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : ((@IN B x t) = (term32 A B x h s)) = ((@IN B x t) = (term32 A B x h s)).
Proof. exact (MK_COMB (@lem5986943 B x t) (@lem5986940 A B x h s)). Qed.
Lemma lem5986945 {A B : Type'} (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term49 A B t h s) = (term49 A B t h s).
Proof. exact (fun_ext (fun x : B => @lem5986944 A B t x h s)). Qed.
Lemma lem5986946 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5986947 {A B : Type'} (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term50 A B t h s) = (term50 A B t h s).
Proof. exact (MK_COMB (@lem5986946 B) (@lem5986945 A B t h s)). Qed.
Lemma lem5986956 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term94 A B C s t g h f x) = (term94 A B C s t g h f x).
Proof. exact (eq_refl (term94 A B C s t g h f x)). Qed.
Lemma lem5986957 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term95 A B C s t g h f) = (term95 A B C s t g h f).
Proof. exact (fun_ext (fun x : A => @lem5986956 A B C s t g h f x)). Qed.
Lemma lem5986958 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5986959 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term38 A B C s t g h f) = (term38 A B C s t g h f).
Proof. exact (MK_COMB (@lem5986958 A) (@lem5986957 A B C s t g h f)). Qed.
Lemma lem5986960 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5986961 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term60 A B C s t g h f) = (term60 A B C s t g h f).
Proof. exact (MK_COMB (@lem5986960) (@lem5986959 A B C s t g h f)). Qed.
Lemma lem5986962 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term62 A B C g f t h s) = (term62 A B C g f t h s).
Proof. exact (MK_COMB (@lem5986961 A B C s t g h f) (@lem5986947 A B t h s)). Qed.
Lemma lem5986967 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term96 A B s h x y) = (term96 A B s h x y).
Proof. exact (eq_refl (term96 A B s h x y)). Qed.
Lemma lem5986968 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term97 A B s h y) = (term97 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5986967 A B s h x y)). Qed.
Lemma lem5986969 {A : Type'} : (@ex1 A) = (@ex1 A).
Proof. exact (eq_refl (@ex1 A)). Qed.
Lemma lem5986970 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term98 A B s h y) = (term98 A B s h y).
Proof. exact (MK_COMB (@lem5986969 A) (@lem5986968 A B s h y)). Qed.
Lemma lem5986973 {B : Type'} (y : B) (t : B -> Prop) : (term99 B y t) = (term99 B y t).
Proof. exact (eq_refl (term99 B y t)). Qed.
Lemma lem5986974 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term100 A B t s h y) = (term100 A B t s h y).
Proof. exact (MK_COMB (@lem5986973 B y t) (@lem5986970 A B s h y)). Qed.
Lemma lem5986975 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term101 A B t s h) = (term101 A B t s h).
Proof. exact (fun_ext (fun y : B => @lem5986974 A B t s h y)). Qed.
Lemma lem5986976 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5986977 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term39 A B t s h) = (term39 A B t s h).
Proof. exact (MK_COMB (@lem5986976 B) (@lem5986975 A B t s h)). Qed.
Lemma lem5986978 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5986979 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term63 A B t s h) = (term63 A B t s h).
Proof. exact (MK_COMB (@lem5986978) (@lem5986977 A B t s h)). Qed.
Lemma lem5986980 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term65 A B C g f t h s) = (term65 A B C g f t h s).
Proof. exact (MK_COMB (@lem5986979 A B t s h) (@lem5986962 A B C g f t h s)). Qed.
Lemma lem5986983 {C : Type'} (op : type1400 C) : (term66 C op) = (term66 C op).
Proof. exact (eq_refl (term66 C op)). Qed.
Lemma lem5986984 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term67 A B C op g f t h s) = (term67 A B C op g f t h s).
Proof. exact (MK_COMB (@lem5986983 C op) (@lem5986980 A B C g f t h s)). Qed.
Lemma lem5986985 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term69 A B C g f t h s) = (term69 A B C g f t h s).
Proof. exact (fun_ext (fun op : type1400 C => @lem5986984 A B C op g f t h s)). Qed.
Lemma lem5986986 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem5986987 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term71 A B C g f t h s) = (term71 A B C g f t h s).
Proof. exact (MK_COMB (@lem5986986 C) (@lem5986985 A B C g f t h s)). Qed.
Lemma lem5986988 {A B C : Type'} (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term73 A B C f t h s) = (term73 A B C f t h s).
Proof. exact (fun_ext (fun g : B -> C => @lem5986987 A B C g f t h s)). Qed.
Lemma lem5986989 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem5986990 {A B C : Type'} (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term75 A B C f t h s) = (term75 A B C f t h s).
Proof. exact (MK_COMB (@lem5986989 B C) (@lem5986988 A B C f t h s)). Qed.
Lemma lem5986991 {A B C : Type'} (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term77 A B C t h s) = (term77 A B C t h s).
Proof. exact (fun_ext (fun f : A -> C => @lem5986990 A B C f t h s)). Qed.
Lemma lem5986992 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem5986993 {A B C : Type'} (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term79 A B C t h s) = (term79 A B C t h s).
Proof. exact (MK_COMB (@lem5986992 A C) (@lem5986991 A B C t h s)). Qed.
Lemma lem5986994 {A B C : Type'} (h : A -> B) (s : A -> Prop) : (term81 A B C h s) = (term81 A B C h s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5986993 A B C t h s)). Qed.
Lemma lem5986995 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5986996 {A B C : Type'} (h : A -> B) (s : A -> Prop) : (term83 A B C h s) = (term83 A B C h s).
Proof. exact (MK_COMB (@lem5986995 B) (@lem5986994 A B C h s)). Qed.
Lemma lem5986997 {A B C : Type'} (s : A -> Prop) : (term85 A B C s) = (term85 A B C s).
Proof. exact (fun_ext (fun h : A -> B => @lem5986996 A B C h s)). Qed.
Lemma lem5986998 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5986999 {A B C : Type'} (s : A -> Prop) : (term87 A B C s) = (term87 A B C s).
Proof. exact (MK_COMB (@lem5986998 A B) (@lem5986997 A B C s)). Qed.
Lemma lem5987000 {A B C : Type'} : (term89 A B C) = (term89 A B C).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5986999 A B C s)). Qed.
Lemma lem5987001 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5987002 {A B C : Type'} : (term91 A B C) = (term91 A B C).
Proof. exact (MK_COMB (@lem5987001 A) (@lem5987000 A B C)). Qed.
Lemma lem5987081 {A B C : Type'} : (term90 A B C) = (term91 A B C).
Proof. exact (TRANS (@lem5986932 A B C) (@lem5987002 A B C)). Qed.
Lemma lem5987082 {A B C : Type'} : (term91 A B C) = (term90 A B C).
Proof. exact (SYM (@lem5987081 A B C)). Qed.
Lemma lem5987084 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (h1 : term39 A B t s h) : term39 A B t s h.
Proof. exact (h1). Qed.
Lemma lem5987085 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term38 A B C s t g h f.
Proof. exact (h1). Qed.
Lemma lem5987087 (p : Prop) : p = (term51 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5987088 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : ((@IN B x t) = (term32 A B x h s)) = (term102 A B t x h s).
Proof. exact (@lem5987087 ((@IN B x t) = (term32 A B x h s))). Qed.
Lemma lem5987089 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term102 A B t x h s) = ((@IN B x t) = (term32 A B x h s)).
Proof. exact (SYM (@lem5987088 A B t x h s)). Qed.
Lemma lem5987090 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term103 A B t x h s) : term103 A B t x h s.
Proof. exact (h1). Qed.
Lemma lem5987106 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term104 A B s h x y) = (term105 A B s h x y).
Proof. exact (@lem17045 (@IN A x s) ((h x) = y)). Qed.
Lemma lem5987111 {A : Type'} (x' : A) (x : A) : (x' = x) = (x' = x).
Proof. exact (eq_refl (x' = x)). Qed.
Lemma lem5987112 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term106 A B s h y x) = (term96 A B s h x y).
Proof. exact (eq_refl (term106 A B s h y x)). Qed.
Lemma lem5987113 {A B : Type'} (s : A -> Prop) (h : A -> B) (x' : A) (y : B) : (term106 A B s h y x') = (term96 A B s h x' y).
Proof. exact (eq_refl (term106 A B s h y x')). Qed.
Lemma lem5987114 {A B : Type'} (s : A -> Prop) (h : A -> B) (x' : A) (y : B) : (term104 A B s h x' y) = (term105 A B s h x' y).
Proof. exact (@lem5987106 A B s h x' y). Qed.
Lemma lem5987115 {A : Type'} (P : A -> Prop) : (@ex1 A P) = (term107 A P).
Proof. exact (@lem18897 A P). Qed.
Lemma lem5987116 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term98 A B s h y) = (term108 A B s h y).
Proof. exact (@lem5987115 A (term97 A B s h y)). Qed.
Lemma lem5987117 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5987118 {A B : Type'} (s : A -> Prop) (h : A -> B) (x' : A) (y : B) : (term109 A B s h y x') = (term104 A B s h x' y).
Proof. exact (MK_COMB (@lem5987117) (@lem5987113 A B s h x' y)). Qed.
Lemma lem5987119 {A B : Type'} (s : A -> Prop) (h : A -> B) (x' : A) (y : B) : (term109 A B s h y x') = (term105 A B s h x' y).
Proof. exact (TRANS (@lem5987118 A B s h x' y) (@lem5987114 A B s h x' y)). Qed.
Lemma lem5987120 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5987121 {A B : Type'} (s : A -> Prop) (h : A -> B) (x' : A) (y : B) : (term110 A B s h y x') = (term111 A B s h x' y).
Proof. exact (MK_COMB (@lem5987120) (@lem5987119 A B s h x' y)). Qed.
Lemma lem5987122 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term112 A B s h y x' x) = (term113 A B s h y x' x).
Proof. exact (MK_COMB (@lem5987121 A B s h x' y) (@lem5987111 A x' x)). Qed.
Lemma lem5987123 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5987124 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term109 A B s h y x) = (term104 A B s h x y).
Proof. exact (MK_COMB (@lem5987123) (@lem5987112 A B s h x y)). Qed.
Lemma lem5987125 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term109 A B s h y x) = (term105 A B s h x y).
Proof. exact (TRANS (@lem5987124 A B s h x y) (@lem5987106 A B s h x y)). Qed.
Lemma lem5987126 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5987127 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term110 A B s h y x) = (term111 A B s h x y).
Proof. exact (MK_COMB (@lem5987126) (@lem5987125 A B s h x y)). Qed.
Lemma lem5987128 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term114 A B s h y x' x) = (term115 A B s h y x' x).
Proof. exact (MK_COMB (@lem5987127 A B s h x y) (@lem5987122 A B s h y x' x)). Qed.
Lemma lem5987129 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term116 A B s h y x) = (term117 A B s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5987128 A B s h y x' x)). Qed.
Lemma lem5987130 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5987131 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term118 A B s h y x) = (term119 A B s h y x).
Proof. exact (MK_COMB (@lem5987130 A) (@lem5987129 A B s h y x)). Qed.
Lemma lem5987132 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term120 A B s h y) = (term121 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5987131 A B s h y x)). Qed.
Lemma lem5987133 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5987134 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term122 A B s h y) = (term123 A B s h y).
Proof. exact (MK_COMB (@lem5987133 A) (@lem5987132 A B s h y)). Qed.
Lemma lem5987135 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term106 A B s h y x) = (term96 A B s h x y).
Proof. exact (eq_refl (term106 A B s h y x)). Qed.
Lemma lem5987136 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term124 A B s h y) = (term97 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5987135 A B s h x y)). Qed.
Lemma lem5987137 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5987138 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term125 A B s h y) = (term126 A B s h y).
Proof. exact (MK_COMB (@lem5987137 A) (@lem5987136 A B s h y)). Qed.
Lemma lem5987139 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5987140 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term127 A B s h y) = (term128 A B s h y).
Proof. exact (MK_COMB (@lem5987139) (@lem5987138 A B s h y)). Qed.
Lemma lem5987141 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term108 A B s h y) = (term129 A B s h y).
Proof. exact (MK_COMB (@lem5987140 A B s h y) (@lem5987134 A B s h y)). Qed.
Lemma lem5987142 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term98 A B s h y) = (term129 A B s h y).
Proof. exact (TRANS (@lem5987116 A B s h y) (@lem5987141 A B s h y)). Qed.
Lemma lem5987144 {B : Type'} (y : B) (t : B -> Prop) : (term130 B y t) = (term130 B y t).
Proof. exact (eq_refl (term130 B y t)). Qed.
Lemma lem5987145 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term131 A B t s h y) = (term132 A B t s h y).
Proof. exact (MK_COMB (@lem5987144 B y t) (@lem5987142 A B s h y)). Qed.
Lemma lem5987146 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term100 A B t s h y) = (term131 A B t s h y).
Proof. exact (@lem17265 (@IN B y t) (term98 A B s h y)). Qed.
Lemma lem5987147 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term100 A B t s h y) = (term132 A B t s h y).
Proof. exact (TRANS (@lem5987146 A B t s h y) (@lem5987145 A B t s h y)). Qed.
Lemma lem5987148 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term101 A B t s h) = (term133 A B t s h).
Proof. exact (fun_ext (fun y : B => @lem5987147 A B t s h y)). Qed.
Lemma lem5987149 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5987150 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term39 A B t s h) = (term134 A B t s h).
Proof. exact (MK_COMB (@lem5987149 B) (@lem5987148 A B t s h)). Qed.
Lemma lem5987252 {A : Type'} (P : Prop) (Q : A -> Prop) : (term135 A P Q) = (term136 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem5987253 {A : Type'} (P : Prop) (Q : A -> Prop) : (term135 A P Q) = (term136 A P Q).
Proof. exact (@lem5987252 A P Q). Qed.
Lemma lem5987254 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term137 A B s h y x) = (term138 A B s h y x).
Proof. exact (@lem5987253 A (term105 A B s h x y) (term139 A B s h y x)). Qed.
Lemma lem5987255 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term140 A B s h y x x') = (term113 A B s h y x' x).
Proof. exact (eq_refl (term140 A B s h y x x')). Qed.
Lemma lem5987256 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term111 A B s h x y) = (term111 A B s h x y).
Proof. exact (eq_refl (term111 A B s h x y)). Qed.
Lemma lem5987257 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term141 A B s h y x x') = (term115 A B s h y x' x).
Proof. exact (MK_COMB (@lem5987256 A B s h x y) (@lem5987255 A B s h y x' x)). Qed.
Lemma lem5987258 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term142 A B s h y x) = (term117 A B s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5987257 A B s h y x' x)). Qed.
Lemma lem5987259 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5987260 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term137 A B s h y x) = (term119 A B s h y x).
Proof. exact (MK_COMB (@lem5987259 A) (@lem5987258 A B s h y x)). Qed.
Lemma lem5987261 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5987262 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term143 A B s h y x) = (term144 A B s h y x).
Proof. exact (MK_COMB (@lem5987261) (@lem5987260 A B s h y x)). Qed.
Lemma lem5987263 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term140 A B s h y x x') = (term113 A B s h y x' x).
Proof. exact (eq_refl (term140 A B s h y x x')). Qed.
Lemma lem5987264 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term145 A B s h y x) = (term139 A B s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5987263 A B s h y x' x)). Qed.
Lemma lem5987265 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5987266 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term146 A B s h y x) = (term147 A B s h y x).
Proof. exact (MK_COMB (@lem5987265 A) (@lem5987264 A B s h y x)). Qed.
Lemma lem5987267 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term111 A B s h x y) = (term111 A B s h x y).
Proof. exact (eq_refl (term111 A B s h x y)). Qed.
Lemma lem5987268 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term138 A B s h y x) = (term148 A B s h y x).
Proof. exact (MK_COMB (@lem5987267 A B s h x y) (@lem5987266 A B s h y x)). Qed.
Lemma lem5987269 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : ((term137 A B s h y x) = (term138 A B s h y x)) = ((term119 A B s h y x) = (term148 A B s h y x)).
Proof. exact (MK_COMB (@lem5987262 A B s h y x) (@lem5987268 A B s h y x)). Qed.
Lemma lem5987270 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term119 A B s h y x) = (term148 A B s h y x).
Proof. exact (EQ_MP (@lem5987269 A B s h y x) (@lem5987254 A B s h y x)). Qed.
Lemma lem5987319 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term121 A B s h y) = (term149 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5987270 A B s h y x)). Qed.
Lemma lem5987320 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5987321 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term123 A B s h y) = (term150 A B s h y).
Proof. exact (MK_COMB (@lem5987320 A) (@lem5987319 A B s h y)). Qed.
Lemma lem5987370 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term128 A B s h y) = (term128 A B s h y).
Proof. exact (eq_refl (term128 A B s h y)). Qed.
Lemma lem5987371 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term129 A B s h y) = (term151 A B s h y).
Proof. exact (MK_COMB (@lem5987370 A B s h y) (@lem5987321 A B s h y)). Qed.
Lemma lem5987372 {B : Type'} (y : B) (t : B -> Prop) : (term130 B y t) = (term130 B y t).
Proof. exact (eq_refl (term130 B y t)). Qed.
Lemma lem5987373 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term132 A B t s h y) = (term152 A B t s h y).
Proof. exact (MK_COMB (@lem5987372 B y t) (@lem5987371 A B s h y)). Qed.
Lemma lem5987374 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term133 A B t s h) = (term153 A B t s h).
Proof. exact (fun_ext (fun y : B => @lem5987373 A B t s h y)). Qed.
Lemma lem5987375 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5987376 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term134 A B t s h) = (term154 A B t s h).
Proof. exact (MK_COMB (@lem5987375 B) (@lem5987374 A B t s h)). Qed.
Lemma lem5987426 {A : Type'} (P : A -> Prop) (Q : Prop) : (term155 A P Q) = (term156 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5987427 {A : Type'} (P : A -> Prop) (Q : Prop) : (term155 A P Q) = (term156 A P Q).
Proof. exact (@lem5987426 A P Q). Qed.
Lemma lem5987428 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term157 A B s h y) = (term158 A B s h y).
Proof. exact (@lem5987427 A (term97 A B s h y) (term150 A B s h y)). Qed.
Lemma lem5987429 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term106 A B s h y x) = (term96 A B s h x y).
Proof. exact (eq_refl (term106 A B s h y x)). Qed.
Lemma lem5987430 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term124 A B s h y) = (term97 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5987429 A B s h x y)). Qed.
Lemma lem5987431 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5987432 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term125 A B s h y) = (term126 A B s h y).
Proof. exact (MK_COMB (@lem5987431 A) (@lem5987430 A B s h y)). Qed.
Lemma lem5987433 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5987434 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term127 A B s h y) = (term128 A B s h y).
Proof. exact (MK_COMB (@lem5987433) (@lem5987432 A B s h y)). Qed.
Lemma lem5987435 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term150 A B s h y) = (term150 A B s h y).
Proof. exact (eq_refl (term150 A B s h y)). Qed.
Lemma lem5987436 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term157 A B s h y) = (term151 A B s h y).
Proof. exact (MK_COMB (@lem5987434 A B s h y) (@lem5987435 A B s h y)). Qed.
Lemma lem5987437 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5987438 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term159 A B s h y) = (term160 A B s h y).
Proof. exact (MK_COMB (@lem5987437) (@lem5987436 A B s h y)). Qed.
Lemma lem5987439 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term106 A B s h y x) = (term96 A B s h x y).
Proof. exact (eq_refl (term106 A B s h y x)). Qed.
Lemma lem5987440 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5987441 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term161 A B s h y x) = (term162 A B s h x y).
Proof. exact (MK_COMB (@lem5987440) (@lem5987439 A B s h x y)). Qed.
Lemma lem5987442 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term150 A B s h y) = (term150 A B s h y).
Proof. exact (eq_refl (term150 A B s h y)). Qed.
Lemma lem5987443 {A B : Type'} (x : A) (s : A -> Prop) (h : A -> B) (y : B) : (term163 A B x s h y) = (term164 A B x s h y).
Proof. exact (MK_COMB (@lem5987441 A B s h x y) (@lem5987442 A B s h y)). Qed.
Lemma lem5987444 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term165 A B s h y) = (term166 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5987443 A B x s h y)). Qed.
Lemma lem5987445 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5987446 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term158 A B s h y) = (term167 A B s h y).
Proof. exact (MK_COMB (@lem5987445 A) (@lem5987444 A B s h y)). Qed.
Lemma lem5987447 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : ((term157 A B s h y) = (term158 A B s h y)) = ((term151 A B s h y) = (term167 A B s h y)).
Proof. exact (MK_COMB (@lem5987438 A B s h y) (@lem5987446 A B s h y)). Qed.
Lemma lem5987448 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term151 A B s h y) = (term167 A B s h y).
Proof. exact (EQ_MP (@lem5987447 A B s h y) (@lem5987428 A B s h y)). Qed.
Lemma lem5987449 {B : Type'} (y : B) (t : B -> Prop) : (term130 B y t) = (term130 B y t).
Proof. exact (eq_refl (term130 B y t)). Qed.
Lemma lem5987450 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term152 A B t s h y) = (term168 A B t s h y).
Proof. exact (MK_COMB (@lem5987449 B y t) (@lem5987448 A B s h y)). Qed.
Lemma lem5987452 {A : Type'} (P : Prop) (Q : A -> Prop) : (term169 A P Q) = (term170 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5987453 {A : Type'} (P : Prop) (Q : A -> Prop) : (term169 A P Q) = (term170 A P Q).
Proof. exact (@lem5987452 A P Q). Qed.
Lemma lem5987454 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term171 A B t s h y) = (term172 A B t s h y).
Proof. exact (@lem5987453 A (term173 B y t) (term166 A B s h y)). Qed.
Lemma lem5987455 {A B : Type'} (x : A) (s : A -> Prop) (h : A -> B) (y : B) : (term174 A B s h y x) = (term164 A B x s h y).
Proof. exact (eq_refl (term174 A B s h y x)). Qed.
Lemma lem5987456 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term175 A B s h y) = (term166 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5987455 A B x s h y)). Qed.
Lemma lem5987457 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5987458 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term176 A B s h y) = (term167 A B s h y).
Proof. exact (MK_COMB (@lem5987457 A) (@lem5987456 A B s h y)). Qed.
Lemma lem5987459 {B : Type'} (y : B) (t : B -> Prop) : (term130 B y t) = (term130 B y t).
Proof. exact (eq_refl (term130 B y t)). Qed.
Lemma lem5987460 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term171 A B t s h y) = (term168 A B t s h y).
Proof. exact (MK_COMB (@lem5987459 B y t) (@lem5987458 A B s h y)). Qed.
Lemma lem5987461 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5987462 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term177 A B t s h y) = (term178 A B t s h y).
Proof. exact (MK_COMB (@lem5987461) (@lem5987460 A B t s h y)). Qed.
Lemma lem5987463 {A B : Type'} (x : A) (s : A -> Prop) (h : A -> B) (y : B) : (term174 A B s h y x) = (term164 A B x s h y).
Proof. exact (eq_refl (term174 A B s h y x)). Qed.
Lemma lem5987464 {B : Type'} (y : B) (t : B -> Prop) : (term130 B y t) = (term130 B y t).
Proof. exact (eq_refl (term130 B y t)). Qed.
Lemma lem5987465 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (h : A -> B) (y : B) : (term179 A B t s h y x) = (term180 A B t x s h y).
Proof. exact (MK_COMB (@lem5987464 B y t) (@lem5987463 A B x s h y)). Qed.
Lemma lem5987466 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term181 A B t s h y) = (term182 A B t s h y).
Proof. exact (fun_ext (fun x : A => @lem5987465 A B t x s h y)). Qed.
Lemma lem5987467 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5987468 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term172 A B t s h y) = (term183 A B t s h y).
Proof. exact (MK_COMB (@lem5987467 A) (@lem5987466 A B t s h y)). Qed.
Lemma lem5987469 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : ((term171 A B t s h y) = (term172 A B t s h y)) = ((term168 A B t s h y) = (term183 A B t s h y)).
Proof. exact (MK_COMB (@lem5987462 A B t s h y) (@lem5987468 A B t s h y)). Qed.
Lemma lem5987470 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term168 A B t s h y) = (term183 A B t s h y).
Proof. exact (EQ_MP (@lem5987469 A B t s h y) (@lem5987454 A B t s h y)). Qed.
Lemma lem5987471 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term152 A B t s h y) = (term183 A B t s h y).
Proof. exact (TRANS (@lem5987450 A B t s h y) (@lem5987470 A B t s h y)). Qed.
Lemma lem5987472 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term153 A B t s h) = (term184 A B t s h).
Proof. exact (fun_ext (fun y : B => @lem5987471 A B t s h y)). Qed.
Lemma lem5987473 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5987474 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term154 A B t s h) = (term185 A B t s h).
Proof. exact (MK_COMB (@lem5987473 B) (@lem5987472 A B t s h)). Qed.
Lemma lem5987476 {A B : Type'} (P : type1413 A B) : (term186 A B P) = (term187 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5987477 {A B : Type'} (P : type1470 A B) : (term188 A B P) = (term189 A B P).
Proof. exact (@lem5987476 B A P). Qed.
Lemma lem5987478 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term190 A B t s h) = (term191 A B t s h).
Proof. exact (@lem5987477 A B (term192 A B t s h)). Qed.
Lemma lem5987479 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term193 A B t s h y) = (term182 A B t s h y).
Proof. exact (eq_refl (term193 A B t s h y)). Qed.
Lemma lem5987480 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5987481 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term194 A B t s h y x) = (term195 A B t s h y x).
Proof. exact (MK_COMB (@lem5987479 A B t s h y) (@lem5987480 A x)). Qed.
Lemma lem5987482 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (h : A -> B) (y : B) : (term195 A B t s h y x) = (term180 A B t x s h y).
Proof. exact (eq_refl (term195 A B t s h y x)). Qed.
Lemma lem5987483 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (h : A -> B) (y : B) : (term194 A B t s h y x) = (term180 A B t x s h y).
Proof. exact (TRANS (@lem5987481 A B t s h y x) (@lem5987482 A B t x s h y)). Qed.
Lemma lem5987484 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term196 A B t s h y) = (term182 A B t s h y).
Proof. exact (fun_ext (fun x : A => @lem5987483 A B t x s h y)). Qed.
Lemma lem5987485 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5987486 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term197 A B t s h y) = (term183 A B t s h y).
Proof. exact (MK_COMB (@lem5987485 A) (@lem5987484 A B t s h y)). Qed.
Lemma lem5987487 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term198 A B t s h) = (term184 A B t s h).
Proof. exact (fun_ext (fun y : B => @lem5987486 A B t s h y)). Qed.
Lemma lem5987488 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5987489 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term190 A B t s h) = (term185 A B t s h).
Proof. exact (MK_COMB (@lem5987488 B) (@lem5987487 A B t s h)). Qed.
Lemma lem5987490 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5987491 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term199 A B t s h) = (term200 A B t s h).
Proof. exact (MK_COMB (@lem5987490) (@lem5987489 A B t s h)). Qed.
Lemma lem5987492 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term193 A B t s h y) = (term182 A B t s h y).
Proof. exact (eq_refl (term193 A B t s h y)). Qed.
Lemma lem5987493 {A B : Type'} (x : B -> A) (y : B) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem5987494 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (x : B -> A) (y : B) : (term201 A B t s h x y) = (term202 A B t s h x y).
Proof. exact (MK_COMB (@lem5987492 A B t s h y) (@lem5987493 A B x y)). Qed.
Lemma lem5987495 {A B : Type'} (t : B -> Prop) (x : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term202 A B t s h x y) = (term203 A B t x s h y).
Proof. exact (eq_refl (term202 A B t s h x y)). Qed.
Lemma lem5987496 {A B : Type'} (t : B -> Prop) (x : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term201 A B t s h x y) = (term203 A B t x s h y).
Proof. exact (TRANS (@lem5987494 A B t s h x y) (@lem5987495 A B t x s h y)). Qed.
Lemma lem5987497 {A B : Type'} (t : B -> Prop) (x : B -> A) (s : A -> Prop) (h : A -> B) : (term204 A B t s h x) = (term205 A B t x s h).
Proof. exact (fun_ext (fun y : B => @lem5987496 A B t x s h y)). Qed.
Lemma lem5987498 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5987499 {A B : Type'} (t : B -> Prop) (x : B -> A) (s : A -> Prop) (h : A -> B) : (term206 A B t s h x) = (term207 A B t x s h).
Proof. exact (MK_COMB (@lem5987498 B) (@lem5987497 A B t x s h)). Qed.
Lemma lem5987500 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term208 A B t s h) = (term209 A B t s h).
Proof. exact (fun_ext (fun x : B -> A => @lem5987499 A B t x s h)). Qed.
Lemma lem5987501 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5987502 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term191 A B t s h) = (term210 A B t s h).
Proof. exact (MK_COMB (@lem5987501 A B) (@lem5987500 A B t s h)). Qed.
Lemma lem5987503 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : ((term190 A B t s h) = (term191 A B t s h)) = ((term185 A B t s h) = (term210 A B t s h)).
Proof. exact (MK_COMB (@lem5987491 A B t s h) (@lem5987502 A B t s h)). Qed.
Lemma lem5987504 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term185 A B t s h) = (term210 A B t s h).
Proof. exact (EQ_MP (@lem5987503 A B t s h) (@lem5987478 A B t s h)). Qed.
Lemma lem5987505 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term154 A B t s h) = (term210 A B t s h).
Proof. exact (TRANS (@lem5987474 A B t s h) (@lem5987504 A B t s h)). Qed.
Lemma lem5987506 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term134 A B t s h) = (term210 A B t s h).
Proof. exact (TRANS (@lem5987376 A B t s h) (@lem5987505 A B t s h)). Qed.
Lemma lem5987507 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term39 A B t s h) = (term210 A B t s h).
Proof. exact (TRANS (@lem5987150 A B t s h) (@lem5987506 A B t s h)). Qed.
Lemma lem5987508 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (h1 : term39 A B t s h) : term210 A B t s h.
Proof. exact (EQ_MP (@lem5987507 A B t s h) (@lem5987084 A B t s h h1)). Qed.
Lemma lem5987519 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term94 A B C s t g h f x) = (term211 A B C s t g h f x).
Proof. exact (@lem17265 (@IN A x s) (term212 A B C t g h f x)). Qed.
Lemma lem5987520 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term95 A B C s t g h f) = (term213 A B C s t g h f).
Proof. exact (fun_ext (fun x : A => @lem5987519 A B C s t g h f x)). Qed.
Lemma lem5987521 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5987574 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term38 A B C s t g h f) = (term214 A B C s t g h f).
Proof. exact (MK_COMB (@lem5987521 A) (@lem5987520 A B C s t g h f)). Qed.
Lemma lem5987575 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term214 A B C s t g h f.
Proof. exact (EQ_MP (@lem5987574 A B C s t g h f) (@lem5987085 A B C s t g h f h1)). Qed.
Lemma lem5987586 {A B : Type'} (x : B) (h : A -> B) (x' : A) (s : A -> Prop) : (term215 A B x h x' s) = (term216 A B x h x' s).
Proof. exact (@lem17045 (x = (h x')) (@IN A x' s)). Qed.
Lemma lem5987589 {A B : Type'} (x : B) (h : A -> B) (x' : A) (s : A -> Prop) : (term92 A B x h x' s) = (term92 A B x h x' s).
Proof. exact (eq_refl (term92 A B x h x' s)). Qed.
Lemma lem5987590 {A : Type'} (P : A -> Prop) : (term217 A P) = (term218 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem5987591 {A B : Type'} (x : B) (h : A -> B) (s : A -> Prop) : (term219 A B x h s) = (term220 A B x h s).
Proof. exact (@lem5987590 A (term93 A B x h s)). Qed.
Lemma lem5987592 {A B : Type'} (x : B) (h : A -> B) (x' : A) (s : A -> Prop) : (term221 A B x h s x') = (term92 A B x h x' s).
Proof. exact (eq_refl (term221 A B x h s x')). Qed.
Lemma lem5987593 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5987594 {A B : Type'} (x : B) (h : A -> B) (x' : A) (s : A -> Prop) : (term222 A B x h s x') = (term215 A B x h x' s).
Proof. exact (MK_COMB (@lem5987593) (@lem5987592 A B x h x' s)). Qed.
Lemma lem5987595 {A B : Type'} (x : B) (h : A -> B) (x' : A) (s : A -> Prop) : (term222 A B x h s x') = (term216 A B x h x' s).
Proof. exact (TRANS (@lem5987594 A B x h x' s) (@lem5987586 A B x h x' s)). Qed.
Lemma lem5987596 {A B : Type'} (x : B) (h : A -> B) (s : A -> Prop) : (term223 A B x h s) = (term224 A B x h s).
Proof. exact (fun_ext (fun x' : A => @lem5987595 A B x h x' s)). Qed.
Lemma lem5987597 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5987598 {A B : Type'} (x : B) (h : A -> B) (s : A -> Prop) : (term220 A B x h s) = (term225 A B x h s).
Proof. exact (MK_COMB (@lem5987597 A) (@lem5987596 A B x h s)). Qed.
Lemma lem5987599 {A B : Type'} (x : B) (h : A -> B) (s : A -> Prop) : (term219 A B x h s) = (term225 A B x h s).
Proof. exact (TRANS (@lem5987591 A B x h s) (@lem5987598 A B x h s)). Qed.
Lemma lem5987600 {A B : Type'} (x : B) (h : A -> B) (s : A -> Prop) : (term93 A B x h s) = (term93 A B x h s).
Proof. exact (fun_ext (fun x' : A => @lem5987589 A B x h x' s)). Qed.
Lemma lem5987601 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5987602 {A B : Type'} (x : B) (h : A -> B) (s : A -> Prop) : (term32 A B x h s) = (term32 A B x h s).
Proof. exact (MK_COMB (@lem5987601 A) (@lem5987600 A B x h s)). Qed.
Lemma lem5987604 {B : Type'} (x : B) (t : B -> Prop) : (term226 B x t) = (term226 B x t).
Proof. exact (eq_refl (term226 B x t)). Qed.
Lemma lem5987605 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term227 A B t x h s) = (term227 A B t x h s).
Proof. exact (MK_COMB (@lem5987604 B x t) (@lem5987602 A B x h s)). Qed.
Lemma lem5987607 {B : Type'} (x : B) (t : B -> Prop) : (term228 B x t) = (term228 B x t).
Proof. exact (eq_refl (term228 B x t)). Qed.
Lemma lem5987608 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term229 A B t x h s) = (term230 A B t x h s).
Proof. exact (MK_COMB (@lem5987607 B x t) (@lem5987599 A B x h s)). Qed.
Lemma lem5987609 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5987610 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term231 A B t x h s) = (term232 A B t x h s).
Proof. exact (MK_COMB (@lem5987609) (@lem5987608 A B t x h s)). Qed.
Lemma lem5987611 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term233 A B t x h s) = (term234 A B t x h s).
Proof. exact (MK_COMB (@lem5987610 A B t x h s) (@lem5987605 A B t x h s)). Qed.
Lemma lem5987612 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term103 A B t x h s) = (term233 A B t x h s).
Proof. exact (@lem17646 (@IN B x t) (term32 A B x h s)). Qed.
Lemma lem5987613 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term103 A B t x h s) = (term234 A B t x h s).
Proof. exact (TRANS (@lem5987612 A B t x h s) (@lem5987611 A B t x h s)). Qed.
Lemma lem5987712 {A : Type'} (P : Prop) (Q : A -> Prop) : (term235 A P Q) = (term236 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5987713 {A : Type'} (P : Prop) (Q : A -> Prop) : (term235 A P Q) = (term236 A P Q).
Proof. exact (@lem5987712 A P Q). Qed.
Lemma lem5987714 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term237 A B t x h s) = (term238 A B t x h s).
Proof. exact (@lem5987713 A (term173 B x t) (term93 A B x h s)). Qed.
Lemma lem5987715 {A B : Type'} (x : B) (h : A -> B) (x' : A) (s : A -> Prop) : (term221 A B x h s x') = (term92 A B x h x' s).
Proof. exact (eq_refl (term221 A B x h s x')). Qed.
Lemma lem5987716 {A B : Type'} (x : B) (h : A -> B) (s : A -> Prop) : (term239 A B x h s) = (term93 A B x h s).
Proof. exact (fun_ext (fun x' : A => @lem5987715 A B x h x' s)). Qed.
Lemma lem5987717 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5987718 {A B : Type'} (x : B) (h : A -> B) (s : A -> Prop) : (term240 A B x h s) = (term32 A B x h s).
Proof. exact (MK_COMB (@lem5987717 A) (@lem5987716 A B x h s)). Qed.
Lemma lem5987719 {B : Type'} (x : B) (t : B -> Prop) : (term226 B x t) = (term226 B x t).
Proof. exact (eq_refl (term226 B x t)). Qed.
Lemma lem5987720 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term237 A B t x h s) = (term227 A B t x h s).
Proof. exact (MK_COMB (@lem5987719 B x t) (@lem5987718 A B x h s)). Qed.
Lemma lem5987721 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5987722 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term241 A B t x h s) = (term242 A B t x h s).
Proof. exact (MK_COMB (@lem5987721) (@lem5987720 A B t x h s)). Qed.
Lemma lem5987723 {A B : Type'} (x : B) (h : A -> B) (x' : A) (s : A -> Prop) : (term221 A B x h s x') = (term92 A B x h x' s).
Proof. exact (eq_refl (term221 A B x h s x')). Qed.
Lemma lem5987724 {B : Type'} (x : B) (t : B -> Prop) : (term226 B x t) = (term226 B x t).
Proof. exact (eq_refl (term226 B x t)). Qed.
Lemma lem5987725 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) : (term243 A B t x h s x') = (term244 A B t x h x' s).
Proof. exact (MK_COMB (@lem5987724 B x t) (@lem5987723 A B x h x' s)). Qed.
Lemma lem5987726 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term245 A B t x h s) = (term246 A B t x h s).
Proof. exact (fun_ext (fun x' : A => @lem5987725 A B t x h x' s)). Qed.
Lemma lem5987727 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5987728 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term238 A B t x h s) = (term247 A B t x h s).
Proof. exact (MK_COMB (@lem5987727 A) (@lem5987726 A B t x h s)). Qed.
Lemma lem5987729 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : ((term237 A B t x h s) = (term238 A B t x h s)) = ((term227 A B t x h s) = (term247 A B t x h s)).
Proof. exact (MK_COMB (@lem5987722 A B t x h s) (@lem5987728 A B t x h s)). Qed.
Lemma lem5987730 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term227 A B t x h s) = (term247 A B t x h s).
Proof. exact (EQ_MP (@lem5987729 A B t x h s) (@lem5987714 A B t x h s)). Qed.
Lemma lem5987731 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term232 A B t x h s) = (term232 A B t x h s).
Proof. exact (eq_refl (term232 A B t x h s)). Qed.
Lemma lem5987732 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term234 A B t x h s) = (term248 A B t x h s).
Proof. exact (MK_COMB (@lem5987731 A B t x h s) (@lem5987730 A B t x h s)). Qed.
Lemma lem5987734 {A : Type'} (P : Prop) (Q : A -> Prop) : (term169 A P Q) = (term170 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5987735 {A : Type'} (P : Prop) (Q : A -> Prop) : (term169 A P Q) = (term170 A P Q).
Proof. exact (@lem5987734 A P Q). Qed.
Lemma lem5987736 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term249 A B t x h s) = (term250 A B t x h s).
Proof. exact (@lem5987735 A (term230 A B t x h s) (term246 A B t x h s)). Qed.
Lemma lem5987737 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) : (term251 A B t x h s x') = (term244 A B t x h x' s).
Proof. exact (eq_refl (term251 A B t x h s x')). Qed.
Lemma lem5987738 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term252 A B t x h s) = (term246 A B t x h s).
Proof. exact (fun_ext (fun x' : A => @lem5987737 A B t x h x' s)). Qed.
Lemma lem5987739 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5987740 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term253 A B t x h s) = (term247 A B t x h s).
Proof. exact (MK_COMB (@lem5987739 A) (@lem5987738 A B t x h s)). Qed.
Lemma lem5987741 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term232 A B t x h s) = (term232 A B t x h s).
Proof. exact (eq_refl (term232 A B t x h s)). Qed.
Lemma lem5987742 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term249 A B t x h s) = (term248 A B t x h s).
Proof. exact (MK_COMB (@lem5987741 A B t x h s) (@lem5987740 A B t x h s)). Qed.
Lemma lem5987743 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5987744 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term254 A B t x h s) = (term255 A B t x h s).
Proof. exact (MK_COMB (@lem5987743) (@lem5987742 A B t x h s)). Qed.
Lemma lem5987745 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) : (term251 A B t x h s x') = (term244 A B t x h x' s).
Proof. exact (eq_refl (term251 A B t x h s x')). Qed.
Lemma lem5987746 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term232 A B t x h s) = (term232 A B t x h s).
Proof. exact (eq_refl (term232 A B t x h s)). Qed.
Lemma lem5987747 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) : (term256 A B t x h s x') = (term257 A B t x h x' s).
Proof. exact (MK_COMB (@lem5987746 A B t x h s) (@lem5987745 A B t x h x' s)). Qed.
Lemma lem5987748 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term258 A B t x h s) = (term259 A B t x h s).
Proof. exact (fun_ext (fun x' : A => @lem5987747 A B t x h x' s)). Qed.
Lemma lem5987749 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5987750 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term250 A B t x h s) = (term260 A B t x h s).
Proof. exact (MK_COMB (@lem5987749 A) (@lem5987748 A B t x h s)). Qed.
Lemma lem5987751 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : ((term249 A B t x h s) = (term250 A B t x h s)) = ((term248 A B t x h s) = (term260 A B t x h s)).
Proof. exact (MK_COMB (@lem5987744 A B t x h s) (@lem5987750 A B t x h s)). Qed.
Lemma lem5987752 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term248 A B t x h s) = (term260 A B t x h s).
Proof. exact (EQ_MP (@lem5987751 A B t x h s) (@lem5987736 A B t x h s)). Qed.
Lemma lem5987754 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term234 A B t x h s) = (term260 A B t x h s).
Proof. exact (TRANS (@lem5987732 A B t x h s) (@lem5987752 A B t x h s)). Qed.
Lemma lem5987755 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term103 A B t x h s) = (term260 A B t x h s).
Proof. exact (TRANS (@lem5987613 A B t x h s) (@lem5987754 A B t x h s)). Qed.
Lemma lem5987756 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term103 A B t x h s) : term260 A B t x h s.
Proof. exact (EQ_MP (@lem5987755 A B t x h s) (@lem5987090 A B t x h s h1)). Qed.
Lemma lem5987757 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) (h1 : term257 A B t x h x' s) : term257 A B t x h x' s.
Proof. exact (h1). Qed.
Lemma lem5987758 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x'' s h) : term207 A B t x'' s h.
Proof. exact (h1). Qed.
Lemma lem5987793 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term211 A B C s t g h f x) = (term211 A B C s t g h f x).
Proof. exact (eq_refl (term211 A B C s t g h f x)). Qed.
Lemma lem5987794 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term213 A B C s t g h f) = (term213 A B C s t g h f).
Proof. exact (fun_ext (fun x : A => @lem5987793 A B C s t g h f x)). Qed.
Lemma lem5987795 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5987796 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term214 A B C s t g h f) = (term214 A B C s t g h f).
Proof. exact (MK_COMB (@lem5987795 A) (@lem5987794 A B C s t g h f)). Qed.
Lemma lem5987797 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term214 A B C s t g h f.
Proof. exact (EQ_MP (@lem5987796 A B C s t g h f) (@lem5987575 A B C s t g h f h1)). Qed.
Lemma lem5987822 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) : (term244 A B t x h x' s) = (term244 A B t x h x' s).
Proof. exact (eq_refl (term244 A B t x h x' s)). Qed.
Lemma lem5987841 {A B : Type'} (x : B) (h : A -> B) (x' : A) (s : A -> Prop) : (term216 A B x h x' s) = (term216 A B x h x' s).
Proof. exact (eq_refl (term216 A B x h x' s)). Qed.
Lemma lem5987842 {A B : Type'} (x : B) (h : A -> B) (s : A -> Prop) : (term224 A B x h s) = (term224 A B x h s).
Proof. exact (fun_ext (fun x' : A => @lem5987841 A B x h x' s)). Qed.
Lemma lem5987843 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5987844 {A B : Type'} (x : B) (h : A -> B) (s : A -> Prop) : (term225 A B x h s) = (term225 A B x h s).
Proof. exact (MK_COMB (@lem5987843 A) (@lem5987842 A B x h s)). Qed.
Lemma lem5987851 {B : Type'} (x : B) (t : B -> Prop) : (term228 B x t) = (term228 B x t).
Proof. exact (eq_refl (term228 B x t)). Qed.
Lemma lem5987852 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term230 A B t x h s) = (term230 A B t x h s).
Proof. exact (MK_COMB (@lem5987851 B x t) (@lem5987844 A B x h s)). Qed.
Lemma lem5987853 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5987854 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) : (term232 A B t x h s) = (term232 A B t x h s).
Proof. exact (MK_COMB (@lem5987853) (@lem5987852 A B t x h s)). Qed.
Lemma lem5987855 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) : (term257 A B t x h x' s) = (term257 A B t x h x' s).
Proof. exact (MK_COMB (@lem5987854 A B t x h s) (@lem5987822 A B t x h x' s)). Qed.
Lemma lem5987856 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) (h1 : term257 A B t x h x' s) : term257 A B t x h x' s.
Proof. exact (EQ_MP (@lem5987855 A B t x h x' s) (@lem5987757 A B t x h x' s h1)). Qed.
Lemma lem5987883 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term113 A B s h y x' x) = (term113 A B s h y x' x).
Proof. exact (eq_refl (term113 A B s h y x' x)). Qed.
Lemma lem5987884 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term139 A B s h y x) = (term139 A B s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5987883 A B s h y x' x)). Qed.
Lemma lem5987885 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5987886 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term147 A B s h y x) = (term147 A B s h y x).
Proof. exact (MK_COMB (@lem5987885 A) (@lem5987884 A B s h y x)). Qed.
Lemma lem5987907 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term111 A B s h x y) = (term111 A B s h x y).
Proof. exact (eq_refl (term111 A B s h x y)). Qed.
Lemma lem5987908 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term148 A B s h y x) = (term148 A B s h y x).
Proof. exact (MK_COMB (@lem5987907 A B s h x y) (@lem5987886 A B s h y x)). Qed.
Lemma lem5987909 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term149 A B s h y) = (term149 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5987908 A B s h y x)). Qed.
Lemma lem5987910 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5987911 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term150 A B s h y) = (term150 A B s h y).
Proof. exact (MK_COMB (@lem5987910 A) (@lem5987909 A B s h y)). Qed.
Lemma lem5987932 {A B : Type'} (s : A -> Prop) (h : A -> B) (x'' : B -> A) (y : B) : (term261 A B s h x'' y) = (term261 A B s h x'' y).
Proof. exact (eq_refl (term261 A B s h x'' y)). Qed.
Lemma lem5987933 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term262 A B x'' s h y) = (term262 A B x'' s h y).
Proof. exact (MK_COMB (@lem5987932 A B s h x'' y) (@lem5987911 A B s h y)). Qed.
Lemma lem5987942 {B : Type'} (y : B) (t : B -> Prop) : (term130 B y t) = (term130 B y t).
Proof. exact (eq_refl (term130 B y t)). Qed.
Lemma lem5987943 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term203 A B t x'' s h y) = (term203 A B t x'' s h y).
Proof. exact (MK_COMB (@lem5987942 B y t) (@lem5987933 A B x'' s h y)). Qed.
Lemma lem5987944 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) : (term205 A B t x'' s h) = (term205 A B t x'' s h).
Proof. exact (fun_ext (fun y : B => @lem5987943 A B t x'' s h y)). Qed.
Lemma lem5987945 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5987946 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) : (term207 A B t x'' s h) = (term207 A B t x'' s h).
Proof. exact (MK_COMB (@lem5987945 B) (@lem5987944 A B t x'' s h)). Qed.
Lemma lem5987947 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x'' s h) : term207 A B t x'' s h.
Proof. exact (EQ_MP (@lem5987946 A B t x'' s h) (@lem5987758 A B t x'' s h h1)). Qed.
Lemma lem5987948 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term230 A B t x h s) : term230 A B t x h s.
Proof. exact (h1). Qed.
Lemma lem5987949 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) (h1 : term244 A B t x h x' s) : term244 A B t x h x' s.
Proof. exact (h1). Qed.
Lemma lem5987950 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term230 A B t x h s) : term225 A B x h s.
Proof. exact (proj2 (@lem5987948 A B t x h s h1)). Qed.
Lemma lem5987952 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) (h1 : term244 A B t x h x' s) : term92 A B x h x' s.
Proof. exact (proj2 (@lem5987949 A B t x h x' s h1)). Qed.
Lemma lem5987984 {A : Type'} (P : Prop) (Q : A -> Prop) : (term136 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5987985 {A : Type'} (P : Prop) (Q : A -> Prop) : (term136 A P Q) = (term135 A P Q).
Proof. exact (@lem5987984 A P Q). Qed.
Lemma lem5987986 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term138 A B s h y x) = (term137 A B s h y x).
Proof. exact (@lem5987985 A (term105 A B s h x y) (term139 A B s h y x)). Qed.
Lemma lem5987987 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term140 A B s h y x x') = (term113 A B s h y x' x).
Proof. exact (eq_refl (term140 A B s h y x x')). Qed.
Lemma lem5987988 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term145 A B s h y x) = (term139 A B s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5987987 A B s h y x' x)). Qed.
Lemma lem5987989 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5987990 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term146 A B s h y x) = (term147 A B s h y x).
Proof. exact (MK_COMB (@lem5987989 A) (@lem5987988 A B s h y x)). Qed.
Lemma lem5987991 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term111 A B s h x y) = (term111 A B s h x y).
Proof. exact (eq_refl (term111 A B s h x y)). Qed.
Lemma lem5987992 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term138 A B s h y x) = (term148 A B s h y x).
Proof. exact (MK_COMB (@lem5987991 A B s h x y) (@lem5987990 A B s h y x)). Qed.
Lemma lem5987993 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5987994 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term263 A B s h y x) = (term264 A B s h y x).
Proof. exact (MK_COMB (@lem5987993) (@lem5987992 A B s h y x)). Qed.
Lemma lem5987995 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term140 A B s h y x x') = (term113 A B s h y x' x).
Proof. exact (eq_refl (term140 A B s h y x x')). Qed.
Lemma lem5987996 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term111 A B s h x y) = (term111 A B s h x y).
Proof. exact (eq_refl (term111 A B s h x y)). Qed.
Lemma lem5987997 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term141 A B s h y x x') = (term115 A B s h y x' x).
Proof. exact (MK_COMB (@lem5987996 A B s h x y) (@lem5987995 A B s h y x' x)). Qed.
Lemma lem5987998 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term142 A B s h y x) = (term117 A B s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5987997 A B s h y x' x)). Qed.
Lemma lem5987999 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5988000 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term137 A B s h y x) = (term119 A B s h y x).
Proof. exact (MK_COMB (@lem5987999 A) (@lem5987998 A B s h y x)). Qed.
Lemma lem5988001 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : ((term138 A B s h y x) = (term137 A B s h y x)) = ((term148 A B s h y x) = (term119 A B s h y x)).
Proof. exact (MK_COMB (@lem5987994 A B s h y x) (@lem5988000 A B s h y x)). Qed.
Lemma lem5988002 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term148 A B s h y x) = (term119 A B s h y x).
Proof. exact (EQ_MP (@lem5988001 A B s h y x) (@lem5987986 A B s h y x)). Qed.
Lemma lem5988003 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term149 A B s h y) = (term121 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5988002 A B s h y x)). Qed.
Lemma lem5988004 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5988005 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term150 A B s h y) = (term123 A B s h y).
Proof. exact (MK_COMB (@lem5988004 A) (@lem5988003 A B s h y)). Qed.
Lemma lem5988006 {A B : Type'} (s : A -> Prop) (h : A -> B) (x'' : B -> A) (y : B) : (term261 A B s h x'' y) = (term261 A B s h x'' y).
Proof. exact (eq_refl (term261 A B s h x'' y)). Qed.
Lemma lem5988007 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term262 A B x'' s h y) = (term265 A B x'' s h y).
Proof. exact (MK_COMB (@lem5988006 A B s h x'' y) (@lem5988005 A B s h y)). Qed.
Lemma lem5988009 {A : Type'} (P : Prop) (Q : A -> Prop) : (term266 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5988010 {A : Type'} (P : Prop) (Q : A -> Prop) : (term266 A P Q) = (term267 A P Q).
Proof. exact (@lem5988009 A P Q). Qed.
Lemma lem5988011 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term268 A B x'' s h y) = (term269 A B x'' s h y).
Proof. exact (@lem5988010 A (term270 A B s h x'' y) (term121 A B s h y)). Qed.
Lemma lem5988012 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term271 A B s h y x) = (term119 A B s h y x).
Proof. exact (eq_refl (term271 A B s h y x)). Qed.
Lemma lem5988013 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term272 A B s h y) = (term121 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5988012 A B s h y x)). Qed.
Lemma lem5988014 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5988015 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term273 A B s h y) = (term123 A B s h y).
Proof. exact (MK_COMB (@lem5988014 A) (@lem5988013 A B s h y)). Qed.
Lemma lem5988016 {A B : Type'} (s : A -> Prop) (h : A -> B) (x'' : B -> A) (y : B) : (term261 A B s h x'' y) = (term261 A B s h x'' y).
Proof. exact (eq_refl (term261 A B s h x'' y)). Qed.
Lemma lem5988017 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term268 A B x'' s h y) = (term265 A B x'' s h y).
Proof. exact (MK_COMB (@lem5988016 A B s h x'' y) (@lem5988015 A B s h y)). Qed.
Lemma lem5988018 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5988019 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term274 A B x'' s h y) = (term275 A B x'' s h y).
Proof. exact (MK_COMB (@lem5988018) (@lem5988017 A B x'' s h y)). Qed.
Lemma lem5988020 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term271 A B s h y x) = (term119 A B s h y x).
Proof. exact (eq_refl (term271 A B s h y x)). Qed.
Lemma lem5988021 {A B : Type'} (s : A -> Prop) (h : A -> B) (x'' : B -> A) (y : B) : (term261 A B s h x'' y) = (term261 A B s h x'' y).
Proof. exact (eq_refl (term261 A B s h x'' y)). Qed.
Lemma lem5988022 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term276 A B x'' s h y x) = (term277 A B x'' s h y x).
Proof. exact (MK_COMB (@lem5988021 A B s h x'' y) (@lem5988020 A B s h y x)). Qed.
Lemma lem5988023 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term278 A B x'' s h y) = (term279 A B x'' s h y).
Proof. exact (fun_ext (fun x : A => @lem5988022 A B x'' s h y x)). Qed.
Lemma lem5988024 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5988025 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term269 A B x'' s h y) = (term280 A B x'' s h y).
Proof. exact (MK_COMB (@lem5988024 A) (@lem5988023 A B x'' s h y)). Qed.
Lemma lem5988026 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : ((term268 A B x'' s h y) = (term269 A B x'' s h y)) = ((term265 A B x'' s h y) = (term280 A B x'' s h y)).
Proof. exact (MK_COMB (@lem5988019 A B x'' s h y) (@lem5988025 A B x'' s h y)). Qed.
Lemma lem5988027 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term265 A B x'' s h y) = (term280 A B x'' s h y).
Proof. exact (EQ_MP (@lem5988026 A B x'' s h y) (@lem5988011 A B x'' s h y)). Qed.
Lemma lem5988029 {A : Type'} (P : Prop) (Q : A -> Prop) : (term266 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5988030 {A : Type'} (P : Prop) (Q : A -> Prop) : (term266 A P Q) = (term267 A P Q).
Proof. exact (@lem5988029 A P Q). Qed.
Lemma lem5988031 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term281 A B x'' s h y x) = (term282 A B x'' s h y x).
Proof. exact (@lem5988030 A (term270 A B s h x'' y) (term117 A B s h y x)). Qed.
Lemma lem5988032 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term283 A B s h y x x') = (term115 A B s h y x' x).
Proof. exact (eq_refl (term283 A B s h y x x')). Qed.
Lemma lem5988033 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term284 A B s h y x) = (term117 A B s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5988032 A B s h y x' x)). Qed.
Lemma lem5988034 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5988035 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term285 A B s h y x) = (term119 A B s h y x).
Proof. exact (MK_COMB (@lem5988034 A) (@lem5988033 A B s h y x)). Qed.
Lemma lem5988036 {A B : Type'} (s : A -> Prop) (h : A -> B) (x'' : B -> A) (y : B) : (term261 A B s h x'' y) = (term261 A B s h x'' y).
Proof. exact (eq_refl (term261 A B s h x'' y)). Qed.
Lemma lem5988037 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term281 A B x'' s h y x) = (term277 A B x'' s h y x).
Proof. exact (MK_COMB (@lem5988036 A B s h x'' y) (@lem5988035 A B s h y x)). Qed.
Lemma lem5988038 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5988039 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term286 A B x'' s h y x) = (term287 A B x'' s h y x).
Proof. exact (MK_COMB (@lem5988038) (@lem5988037 A B x'' s h y x)). Qed.
Lemma lem5988040 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term283 A B s h y x x') = (term115 A B s h y x' x).
Proof. exact (eq_refl (term283 A B s h y x x')). Qed.
Lemma lem5988041 {A B : Type'} (s : A -> Prop) (h : A -> B) (x'' : B -> A) (y : B) : (term261 A B s h x'' y) = (term261 A B s h x'' y).
Proof. exact (eq_refl (term261 A B s h x'' y)). Qed.
Lemma lem5988042 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term288 A B x'' s h y x x') = (term289 A B x'' s h y x' x).
Proof. exact (MK_COMB (@lem5988041 A B s h x'' y) (@lem5988040 A B s h y x' x)). Qed.
Lemma lem5988043 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term290 A B x'' s h y x) = (term291 A B x'' s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5988042 A B x'' s h y x' x)). Qed.
Lemma lem5988044 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5988045 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term282 A B x'' s h y x) = (term292 A B x'' s h y x).
Proof. exact (MK_COMB (@lem5988044 A) (@lem5988043 A B x'' s h y x)). Qed.
Lemma lem5988046 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : ((term281 A B x'' s h y x) = (term282 A B x'' s h y x)) = ((term277 A B x'' s h y x) = (term292 A B x'' s h y x)).
Proof. exact (MK_COMB (@lem5988039 A B x'' s h y x) (@lem5988045 A B x'' s h y x)). Qed.
Lemma lem5988047 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term277 A B x'' s h y x) = (term292 A B x'' s h y x).
Proof. exact (EQ_MP (@lem5988046 A B x'' s h y x) (@lem5988031 A B x'' s h y x)). Qed.
Lemma lem5988048 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term279 A B x'' s h y) = (term293 A B x'' s h y).
Proof. exact (fun_ext (fun x : A => @lem5988047 A B x'' s h y x)). Qed.
Lemma lem5988049 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5988050 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term280 A B x'' s h y) = (term294 A B x'' s h y).
Proof. exact (MK_COMB (@lem5988049 A) (@lem5988048 A B x'' s h y)). Qed.
Lemma lem5988051 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term265 A B x'' s h y) = (term294 A B x'' s h y).
Proof. exact (TRANS (@lem5988027 A B x'' s h y) (@lem5988050 A B x'' s h y)). Qed.
Lemma lem5988052 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term262 A B x'' s h y) = (term294 A B x'' s h y).
Proof. exact (TRANS (@lem5988007 A B x'' s h y) (@lem5988051 A B x'' s h y)). Qed.
Lemma lem5988053 {B : Type'} (y : B) (t : B -> Prop) : (term130 B y t) = (term130 B y t).
Proof. exact (eq_refl (term130 B y t)). Qed.
Lemma lem5988054 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term203 A B t x'' s h y) = (term295 A B t x'' s h y).
Proof. exact (MK_COMB (@lem5988053 B y t) (@lem5988052 A B x'' s h y)). Qed.
Lemma lem5988056 {A : Type'} (P : Prop) (Q : A -> Prop) : (term136 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5988057 {A : Type'} (P : Prop) (Q : A -> Prop) : (term136 A P Q) = (term135 A P Q).
Proof. exact (@lem5988056 A P Q). Qed.
Lemma lem5988058 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term296 A B t x'' s h y) = (term297 A B t x'' s h y).
Proof. exact (@lem5988057 A (term173 B y t) (term293 A B x'' s h y)). Qed.
Lemma lem5988059 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term298 A B x'' s h y x) = (term292 A B x'' s h y x).
Proof. exact (eq_refl (term298 A B x'' s h y x)). Qed.
Lemma lem5988060 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term299 A B x'' s h y) = (term293 A B x'' s h y).
Proof. exact (fun_ext (fun x : A => @lem5988059 A B x'' s h y x)). Qed.
Lemma lem5988061 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5988062 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term300 A B x'' s h y) = (term294 A B x'' s h y).
Proof. exact (MK_COMB (@lem5988061 A) (@lem5988060 A B x'' s h y)). Qed.
Lemma lem5988063 {B : Type'} (y : B) (t : B -> Prop) : (term130 B y t) = (term130 B y t).
Proof. exact (eq_refl (term130 B y t)). Qed.
Lemma lem5988064 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term296 A B t x'' s h y) = (term295 A B t x'' s h y).
Proof. exact (MK_COMB (@lem5988063 B y t) (@lem5988062 A B x'' s h y)). Qed.
Lemma lem5988065 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5988066 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term301 A B t x'' s h y) = (term302 A B t x'' s h y).
Proof. exact (MK_COMB (@lem5988065) (@lem5988064 A B t x'' s h y)). Qed.
Lemma lem5988067 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term298 A B x'' s h y x) = (term292 A B x'' s h y x).
Proof. exact (eq_refl (term298 A B x'' s h y x)). Qed.
Lemma lem5988068 {B : Type'} (y : B) (t : B -> Prop) : (term130 B y t) = (term130 B y t).
Proof. exact (eq_refl (term130 B y t)). Qed.
Lemma lem5988069 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term303 A B t x'' s h y x) = (term304 A B t x'' s h y x).
Proof. exact (MK_COMB (@lem5988068 B y t) (@lem5988067 A B x'' s h y x)). Qed.
Lemma lem5988070 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term305 A B t x'' s h y) = (term306 A B t x'' s h y).
Proof. exact (fun_ext (fun x : A => @lem5988069 A B t x'' s h y x)). Qed.
Lemma lem5988071 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5988072 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term297 A B t x'' s h y) = (term307 A B t x'' s h y).
Proof. exact (MK_COMB (@lem5988071 A) (@lem5988070 A B t x'' s h y)). Qed.
Lemma lem5988073 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : ((term296 A B t x'' s h y) = (term297 A B t x'' s h y)) = ((term295 A B t x'' s h y) = (term307 A B t x'' s h y)).
Proof. exact (MK_COMB (@lem5988066 A B t x'' s h y) (@lem5988072 A B t x'' s h y)). Qed.
Lemma lem5988074 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term295 A B t x'' s h y) = (term307 A B t x'' s h y).
Proof. exact (EQ_MP (@lem5988073 A B t x'' s h y) (@lem5988058 A B t x'' s h y)). Qed.
Lemma lem5988076 {A : Type'} (P : Prop) (Q : A -> Prop) : (term136 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5988077 {A : Type'} (P : Prop) (Q : A -> Prop) : (term136 A P Q) = (term135 A P Q).
Proof. exact (@lem5988076 A P Q). Qed.
Lemma lem5988078 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term308 A B t x'' s h y x) = (term309 A B t x'' s h y x).
Proof. exact (@lem5988077 A (term173 B y t) (term291 A B x'' s h y x)). Qed.
Lemma lem5988079 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term310 A B x'' s h y x x') = (term289 A B x'' s h y x' x).
Proof. exact (eq_refl (term310 A B x'' s h y x x')). Qed.
Lemma lem5988080 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term311 A B x'' s h y x) = (term291 A B x'' s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5988079 A B x'' s h y x' x)). Qed.
Lemma lem5988081 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5988082 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term312 A B x'' s h y x) = (term292 A B x'' s h y x).
Proof. exact (MK_COMB (@lem5988081 A) (@lem5988080 A B x'' s h y x)). Qed.
Lemma lem5988083 {B : Type'} (y : B) (t : B -> Prop) : (term130 B y t) = (term130 B y t).
Proof. exact (eq_refl (term130 B y t)). Qed.
Lemma lem5988084 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term308 A B t x'' s h y x) = (term304 A B t x'' s h y x).
Proof. exact (MK_COMB (@lem5988083 B y t) (@lem5988082 A B x'' s h y x)). Qed.
Lemma lem5988085 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5988086 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term313 A B t x'' s h y x) = (term314 A B t x'' s h y x).
Proof. exact (MK_COMB (@lem5988085) (@lem5988084 A B t x'' s h y x)). Qed.
Lemma lem5988087 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term310 A B x'' s h y x x') = (term289 A B x'' s h y x' x).
Proof. exact (eq_refl (term310 A B x'' s h y x x')). Qed.
Lemma lem5988088 {B : Type'} (y : B) (t : B -> Prop) : (term130 B y t) = (term130 B y t).
Proof. exact (eq_refl (term130 B y t)). Qed.
Lemma lem5988089 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term315 A B t x'' s h y x x') = (term316 A B t x'' s h y x' x).
Proof. exact (MK_COMB (@lem5988088 B y t) (@lem5988087 A B x'' s h y x' x)). Qed.
Lemma lem5988090 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term317 A B t x'' s h y x) = (term318 A B t x'' s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5988089 A B t x'' s h y x' x)). Qed.
Lemma lem5988091 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5988092 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term309 A B t x'' s h y x) = (term319 A B t x'' s h y x).
Proof. exact (MK_COMB (@lem5988091 A) (@lem5988090 A B t x'' s h y x)). Qed.
Lemma lem5988093 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : ((term308 A B t x'' s h y x) = (term309 A B t x'' s h y x)) = ((term304 A B t x'' s h y x) = (term319 A B t x'' s h y x)).
Proof. exact (MK_COMB (@lem5988086 A B t x'' s h y x) (@lem5988092 A B t x'' s h y x)). Qed.
Lemma lem5988094 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term304 A B t x'' s h y x) = (term319 A B t x'' s h y x).
Proof. exact (EQ_MP (@lem5988093 A B t x'' s h y x) (@lem5988078 A B t x'' s h y x)). Qed.
Lemma lem5988095 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term306 A B t x'' s h y) = (term320 A B t x'' s h y).
Proof. exact (fun_ext (fun x : A => @lem5988094 A B t x'' s h y x)). Qed.
Lemma lem5988096 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5988097 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term307 A B t x'' s h y) = (term321 A B t x'' s h y).
Proof. exact (MK_COMB (@lem5988096 A) (@lem5988095 A B t x'' s h y)). Qed.
Lemma lem5988098 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term295 A B t x'' s h y) = (term321 A B t x'' s h y).
Proof. exact (TRANS (@lem5988074 A B t x'' s h y) (@lem5988097 A B t x'' s h y)). Qed.
Lemma lem5988099 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term203 A B t x'' s h y) = (term321 A B t x'' s h y).
Proof. exact (TRANS (@lem5988054 A B t x'' s h y) (@lem5988098 A B t x'' s h y)). Qed.
Lemma lem5988100 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) : (term205 A B t x'' s h) = (term322 A B t x'' s h).
Proof. exact (fun_ext (fun y : B => @lem5988099 A B t x'' s h y)). Qed.
Lemma lem5988101 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5988102 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) : (term207 A B t x'' s h) = (term323 A B t x'' s h).
Proof. exact (MK_COMB (@lem5988101 B) (@lem5988100 A B t x'' s h)). Qed.
Lemma lem5988140 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term316 A B t x'' s h y x' x) = (term324 A B x'' t s h y x' x).
Proof. exact (@lem19490 (term270 A B s h x'' y) (term173 B y t) (term115 A B s h y x' x)). Qed.
Lemma lem5988141 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term325 A B t s h y x' x) = (term325 A B t s h y x' x).
Proof. exact (eq_refl (term325 A B t s h y x' x)). Qed.
Lemma lem5988148 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h : A -> B) (x'' : B -> A) (y : B) : (term326 A B t s h x'' y) = (term327 A B s t h x'' y).
Proof. exact (@lem19490 (term328 A B x'' y s) (term173 B y t) ((term329 A B h x'' y) = y)). Qed.
Lemma lem5988149 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5988150 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h : A -> B) (x'' : B -> A) (y : B) : (term330 A B t s h x'' y) = (term331 A B s t h x'' y).
Proof. exact (MK_COMB (@lem5988149) (@lem5988148 A B s t h x'' y)). Qed.
Lemma lem5988151 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term324 A B x'' t s h y x' x) = (term332 A B x'' t s h y x' x).
Proof. exact (MK_COMB (@lem5988150 A B s t h x'' y) (@lem5988141 A B t s h y x' x)). Qed.
Lemma lem5988153 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term316 A B t x'' s h y x' x) = (term332 A B x'' t s h y x' x).
Proof. exact (TRANS (@lem5988140 A B x'' t s h y x' x) (@lem5988151 A B x'' t s h y x' x)). Qed.
Lemma lem5988154 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term318 A B t x'' s h y x) = (term333 A B x'' t s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5988153 A B x'' t s h y x' x)). Qed.
Lemma lem5988155 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5988156 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term319 A B t x'' s h y x) = (term334 A B x'' t s h y x).
Proof. exact (MK_COMB (@lem5988155 A) (@lem5988154 A B x'' t s h y x)). Qed.
Lemma lem5988157 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term320 A B t x'' s h y) = (term335 A B x'' t s h y).
Proof. exact (fun_ext (fun x : A => @lem5988156 A B x'' t s h y x)). Qed.
Lemma lem5988158 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5988159 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term321 A B t x'' s h y) = (term336 A B x'' t s h y).
Proof. exact (MK_COMB (@lem5988158 A) (@lem5988157 A B x'' t s h y)). Qed.
Lemma lem5988160 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term322 A B t x'' s h) = (term337 A B x'' t s h).
Proof. exact (fun_ext (fun y : B => @lem5988159 A B x'' t s h y)). Qed.
Lemma lem5988161 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5988162 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term323 A B t x'' s h) = (term338 A B x'' t s h).
Proof. exact (MK_COMB (@lem5988161 B) (@lem5988160 A B x'' t s h)). Qed.
Lemma lem5988163 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term207 A B t x'' s h) = (term338 A B x'' t s h).
Proof. exact (TRANS (@lem5988102 A B t x'' s h) (@lem5988162 A B x'' t s h)). Qed.
Lemma lem5988164 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x'' s h) : term338 A B x'' t s h.
Proof. exact (EQ_MP (@lem5988163 A B x'' t s h) (@lem5987947 A B t x'' s h h1)). Qed.
Lemma lem5988176 {A B : Type'} (x : B) (h : A -> B) (x' : A) (s : A -> Prop) : (term216 A B x h x' s) = (term216 A B x h x' s).
Proof. exact (eq_refl (term216 A B x h x' s)). Qed.
Lemma lem5988177 {A B : Type'} (x : B) (h : A -> B) (s : A -> Prop) : (term224 A B x h s) = (term224 A B x h s).
Proof. exact (fun_ext (fun x' : A => @lem5988176 A B x h x' s)). Qed.
Lemma lem5988178 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5988180 {A B : Type'} (x : B) (h : A -> B) (s : A -> Prop) : (term225 A B x h s) = (term225 A B x h s).
Proof. exact (MK_COMB (@lem5988178 A) (@lem5988177 A B x h s)). Qed.
Lemma lem5988181 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term230 A B t x h s) : term225 A B x h s.
Proof. exact (EQ_MP (@lem5988180 A B x h s) (@lem5987950 A B t x h s h1)). Qed.
Lemma lem5988203 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term211 A B C s t g h f x) = (term339 A B C t s g h f x).
Proof. exact (@lem19490 (term340 A B h x t) (term173 A x s) ((term341 A B C g h x) = (f x))). Qed.
Lemma lem5988204 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term213 A B C s t g h f) = (term342 A B C t s g h f).
Proof. exact (fun_ext (fun x : A => @lem5988203 A B C t s g h f x)). Qed.
Lemma lem5988205 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5988207 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term214 A B C s t g h f) = (term343 A B C t s g h f).
Proof. exact (MK_COMB (@lem5988205 A) (@lem5988204 A B C t s g h f)). Qed.
Lemma lem5988208 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term343 A B C t s g h f.
Proof. exact (EQ_MP (@lem5988207 A B C t s g h f) (@lem5987797 A B C s t g h f h1)). Qed.
Lemma lem5988406 {A B : Type'} (_76047 : B) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x'' s h) : term344 A B x'' t s h _76047.
Proof. exact (@lem5988164 A B t x'' s h h1 _76047). Qed.
Lemma lem5988407 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (_76047 : B) : (term344 A B x'' t s h _76047) = (term336 A B x'' t s h _76047).
Proof. exact (eq_refl (term344 A B x'' t s h _76047)). Qed.
Lemma lem5988408 {A B : Type'} (_76047 : B) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x'' s h) : term336 A B x'' t s h _76047.
Proof. exact (EQ_MP (@lem5988407 A B x'' t s h _76047) (@lem5988406 A B _76047 t x'' s h h1)). Qed.
Lemma lem5988409 {A B : Type'} (_76047 : B) (_76048 : A) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x'' s h) : term345 A B x'' t s h _76047 _76048.
Proof. exact (@lem5988408 A B _76047 t x'' s h h1 _76048). Qed.
Lemma lem5988410 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (_76047 : B) (_76048 : A) : (term345 A B x'' t s h _76047 _76048) = (term334 A B x'' t s h _76047 _76048).
Proof. exact (eq_refl (term345 A B x'' t s h _76047 _76048)). Qed.
Lemma lem5988411 {A B : Type'} (_76047 : B) (_76048 : A) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x'' s h) : term334 A B x'' t s h _76047 _76048.
Proof. exact (EQ_MP (@lem5988410 A B x'' t s h _76047 _76048) (@lem5988409 A B _76047 _76048 t x'' s h h1)). Qed.
Lemma lem5988412 {A B : Type'} (_76047 : B) (_76048 : A) (_76049 : A) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x'' s h) : term346 A B x'' t s h _76047 _76048 _76049.
Proof. exact (@lem5988411 A B _76047 _76048 t x'' s h h1 _76049). Qed.
Lemma lem5988413 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (_76047 : B) (_76049 : A) (_76048 : A) : (term346 A B x'' t s h _76047 _76048 _76049) = (term332 A B x'' t s h _76047 _76049 _76048).
Proof. exact (eq_refl (term346 A B x'' t s h _76047 _76048 _76049)). Qed.
Lemma lem5988414 {A B : Type'} (_76047 : B) (_76049 : A) (_76048 : A) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x'' s h) : term332 A B x'' t s h _76047 _76049 _76048.
Proof. exact (EQ_MP (@lem5988413 A B x'' t s h _76047 _76049 _76048) (@lem5988412 A B _76047 _76048 _76049 t x'' s h h1)). Qed.
Lemma lem5988415 {A B : Type'} (_76050 : A) (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term230 A B t x h s) : term347 A B x h s _76050.
Proof. exact (@lem5988181 A B t x h s h1 _76050). Qed.
Lemma lem5988416 {A B : Type'} (x : B) (h : A -> B) (_76050 : A) (s : A -> Prop) : (term347 A B x h s _76050) = (term216 A B x h _76050 s).
Proof. exact (eq_refl (term347 A B x h s _76050)). Qed.
Lemma lem5988418 {A B C : Type'} (_76051 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term348 A B C t s g h f _76051.
Proof. exact (@lem5988208 A B C s t g h f h1 _76051). Qed.
Lemma lem5988419 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (_76051 : A) : (term348 A B C t s g h f _76051) = (term339 A B C t s g h f _76051).
Proof. exact (eq_refl (term348 A B C t s g h f _76051)). Qed.
Lemma lem5988420 {A B C : Type'} (_76051 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term339 A B C t s g h f _76051.
Proof. exact (EQ_MP (@lem5988419 A B C t s g h f _76051) (@lem5988418 A B C _76051 s t g h f h1)). Qed.
Lemma lem5988431 {A B : Type'} (_76047 : B) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x'' s h) : term327 A B s t h x'' _76047.
Proof. exact (proj1 (@lem5988414 A B _76047 (@el A) (@el A) t x'' s h h1)). Qed.
Lemma lem5988451 {A B : Type'} (_76050 : A) (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term230 A B t x h s) : term216 A B x h _76050 s.
Proof. exact (EQ_MP (@lem5988416 A B x h _76050 s) (@lem5988415 A B _76050 t x h s h1)). Qed.
Lemma lem5988483 {A B : Type'} (_76047 : B) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x'' s h) : term349 A B t x'' _76047 s.
Proof. exact (proj1 (@lem5988431 A B _76047 t x'' s h h1)). Qed.
Lemma lem5988489 {A B : Type'} (_76047 : B) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x'' s h) : term350 A B t h x'' _76047.
Proof. exact (proj2 (@lem5988431 A B _76047 t x'' s h h1)). Qed.
Lemma lem5988505 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) (h1 : term244 A B t x h x' s) : term173 B x t.
Proof. exact (proj1 (@lem5987949 A B t x h x' s h1)). Qed.
Lemma lem5988507 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) (h1 : term244 A B t x h x' s) : x = (h x').
Proof. exact (proj1 (@lem5987952 A B t x h x' s h1)). Qed.
Lemma lem5988588 {B : Type'} (t : B -> Prop) : (term351 B t) = (term351 B t).
Proof. exact (eq_refl (term351 B t)). Qed.
Lemma lem5988589 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) (h1 : term244 A B t x h x' s) : (term352 B t x) = (term353 A B t h x').
Proof. exact (MK_COMB (@lem5988588 B t) (@lem5988507 A B t x h x' s h1)). Qed.
Lemma lem5988590 {A B : Type'} (h : A -> B) (x' : A) (t : B -> Prop) : (term353 A B t h x') = (term354 A B h x' t).
Proof. exact (eq_refl (term353 A B t h x')). Qed.
Lemma lem5988591 {B : Type'} (t : B -> Prop) (x : B) : (term355 B t x) = (term355 B t x).
Proof. exact (eq_refl (term355 B t x)). Qed.
Lemma lem5988592 {A B : Type'} (x : B) (h : A -> B) (x' : A) (t : B -> Prop) : ((term352 B t x) = (term353 A B t h x')) = ((term352 B t x) = (term354 A B h x' t)).
Proof. exact (MK_COMB (@lem5988591 B t x) (@lem5988590 A B h x' t)). Qed.
Lemma lem5988593 {B : Type'} (x : B) (t : B -> Prop) : (term352 B t x) = (term173 B x t).
Proof. exact (eq_refl (term352 B t x)). Qed.
Lemma lem5988594 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5988595 {B : Type'} (x : B) (t : B -> Prop) : (term355 B t x) = (term356 B x t).
Proof. exact (MK_COMB (@lem5988594) (@lem5988593 B x t)). Qed.
Lemma lem5988596 {A B : Type'} (h : A -> B) (x' : A) (t : B -> Prop) : (term354 A B h x' t) = (term354 A B h x' t).
Proof. exact (eq_refl (term354 A B h x' t)). Qed.
Lemma lem5988597 {A B : Type'} (x : B) (h : A -> B) (x' : A) (t : B -> Prop) : ((term352 B t x) = (term354 A B h x' t)) = ((term173 B x t) = (term354 A B h x' t)).
Proof. exact (MK_COMB (@lem5988595 B x t) (@lem5988596 A B h x' t)). Qed.
Lemma lem5988598 {A B : Type'} (x : B) (h : A -> B) (x' : A) (t : B -> Prop) : ((term352 B t x) = (term353 A B t h x')) = ((term173 B x t) = (term354 A B h x' t)).
Proof. exact (TRANS (@lem5988592 A B x h x' t) (@lem5988597 A B x h x' t)). Qed.
Lemma lem5988599 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) (h1 : term244 A B t x h x' s) : (term173 B x t) = (term354 A B h x' t).
Proof. exact (EQ_MP (@lem5988598 A B x h x' t) (@lem5988589 A B t x h x' s h1)). Qed.
Lemma lem5988600 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) (h1 : term244 A B t x h x' s) : term354 A B h x' t.
Proof. exact (EQ_MP (@lem5988599 A B t x h x' s h1) (@lem5988505 A B t x h x' s h1)). Qed.
Lemma lem5988670 {A B C : Type'} (_76051 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term357 A B s h _76051 t.
Proof. exact (proj1 (@lem5988420 A B C _76051 s t g h f h1)). Qed.
Lemma lem5988768 {B : Type'} (x : B) (y : B) (z : B) : term358 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem5988780 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term230 A B t x h s) : @IN B x t.
Proof. exact (proj1 (@lem5987948 A B t x h s h1)). Qed.
Lemma lem5988781 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term230 A B t x h s) : term359 B x t.
Proof. exact (fun h0 : term173 B x t => @lem5988780 A B t x h s h1). Qed.
Lemma lem5988783 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5988784 {B : Type'} (x : B) (t : B -> Prop) : (term359 B x t) = (@IN B x t).
Proof. exact (@lem5988783 (@IN B x t)). Qed.
Lemma lem5988785 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term230 A B t x h s) : @IN B x t.
Proof. exact (EQ_MP (@lem5988784 B x t) (@lem5988781 A B t x h s h1)). Qed.
Lemma lem5988791 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5988792 {A B : Type'} (h : A -> B) (x'' : B -> A) (_76047 : B) (t : B -> Prop) : (term350 A B t h x'' _76047) = (term361 A B h x'' _76047 t).
Proof. exact (@lem5988791 ((term329 A B h x'' _76047) = _76047) (term173 B _76047 t)). Qed.
Lemma lem5988800 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5988801 {A B : Type'} (h : A -> B) (x'' : B -> A) (_76047 : B) (t : B -> Prop) : (term362 A B t h x'' _76047) = (term363 A B h x'' _76047 t).
Proof. exact (MK_COMB (@lem5988800) (@lem5988792 A B h x'' _76047 t)). Qed.
Lemma lem5988809 {A B : Type'} (h : A -> B) (x'' : B -> A) (_76047 : B) (t : B -> Prop) : (term361 A B h x'' _76047 t) = (term361 A B h x'' _76047 t).
Proof. exact (eq_refl (term361 A B h x'' _76047 t)). Qed.
Lemma lem5988810 {A B : Type'} (h : A -> B) (x'' : B -> A) (_76047 : B) (t : B -> Prop) : ((term350 A B t h x'' _76047) = (term361 A B h x'' _76047 t)) = ((term361 A B h x'' _76047 t) = (term361 A B h x'' _76047 t)).
Proof. exact (MK_COMB (@lem5988801 A B h x'' _76047 t) (@lem5988809 A B h x'' _76047 t)). Qed.
Lemma lem5988812 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5988813 (x : Prop) : (x = x) = True.
Proof. exact (@lem5988812 Prop x). Qed.
Lemma lem5988814 {A B : Type'} (h : A -> B) (x'' : B -> A) (_76047 : B) (t : B -> Prop) : ((term361 A B h x'' _76047 t) = (term361 A B h x'' _76047 t)) = True.
Proof. exact (@lem5988813 (term361 A B h x'' _76047 t)). Qed.
Lemma lem5988815 {A B : Type'} (h : A -> B) (x'' : B -> A) (_76047 : B) (t : B -> Prop) : ((term350 A B t h x'' _76047) = (term361 A B h x'' _76047 t)) = True.
Proof. exact (TRANS (@lem5988810 A B h x'' _76047 t) (@lem5988814 A B h x'' _76047 t)). Qed.
Lemma lem5988816 {A B : Type'} (h : A -> B) (x'' : B -> A) (_76047 : B) (t : B -> Prop) : True = ((term350 A B t h x'' _76047) = (term361 A B h x'' _76047 t)).
Proof. exact (SYM (@lem5988815 A B h x'' _76047 t)). Qed.
Lemma lem5988817 {A B : Type'} (h : A -> B) (x'' : B -> A) (_76047 : B) (t : B -> Prop) : (term350 A B t h x'' _76047) = (term361 A B h x'' _76047 t).
Proof. exact (EQ_MP (@lem5988816 A B h x'' _76047 t) (@lem0)). Qed.
Lemma lem5988818 {A B : Type'} (_76047 : B) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x'' s h) : term361 A B h x'' _76047 t.
Proof. exact (EQ_MP (@lem5988817 A B h x'' _76047 t) (@lem5988489 A B _76047 t x'' s h h1)). Qed.
Lemma lem5988820 (b : Prop) (a : Prop) : (a \/ b) = (term364 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5988821 {A B : Type'} (t : B -> Prop) (h : A -> B) (x'' : B -> A) (_76047 : B) : (term361 A B h x'' _76047 t) = (term365 A B t h x'' _76047).
Proof. exact (@lem5988820 (term173 B _76047 t) ((term329 A B h x'' _76047) = _76047)). Qed.
Lemma lem5988823 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5988824 {B : Type'} (_76047 : B) (t : B -> Prop) : (term366 B _76047 t) = (@IN B _76047 t).
Proof. exact (@lem5988823 (@IN B _76047 t)). Qed.
Lemma lem5988825 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5988826 {B : Type'} (_76047 : B) (t : B -> Prop) : (term367 B _76047 t) = (term99 B _76047 t).
Proof. exact (MK_COMB (@lem5988825) (@lem5988824 B _76047 t)). Qed.
Lemma lem5988827 {A B : Type'} (h : A -> B) (x'' : B -> A) (_76047 : B) : ((term329 A B h x'' _76047) = _76047) = ((term329 A B h x'' _76047) = _76047).
Proof. exact (eq_refl ((term329 A B h x'' _76047) = _76047)). Qed.
Lemma lem5988828 {A B : Type'} (t : B -> Prop) (h : A -> B) (x'' : B -> A) (_76047 : B) : (term365 A B t h x'' _76047) = (term368 A B t h x'' _76047).
Proof. exact (MK_COMB (@lem5988826 B _76047 t) (@lem5988827 A B h x'' _76047)). Qed.
Lemma lem5988829 {A B : Type'} (t : B -> Prop) (h : A -> B) (x'' : B -> A) (_76047 : B) : (term361 A B h x'' _76047 t) = (term368 A B t h x'' _76047).
Proof. exact (TRANS (@lem5988821 A B t h x'' _76047) (@lem5988828 A B t h x'' _76047)). Qed.
Lemma lem5988832 {A B : Type'} (_76047 : B) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x'' s h) : term368 A B t h x'' _76047.
Proof. exact (EQ_MP (@lem5988829 A B t h x'' _76047) (@lem5988818 A B _76047 t x'' s h h1)). Qed.
Lemma lem5988833 {A B : Type'} (_76047 : B) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x'' s h) : term368 A B t h x'' _76047.
Proof. exact (@lem5988832 A B _76047 t x'' s h h1). Qed.
Lemma lem5988834 {A B : Type'} (x : B) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x'' s h) : term368 A B t h x'' x.
Proof. exact (@lem5988833 A B x t x'' s h h1). Qed.
Lemma lem5988837 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term207 A B t x'' s h) (h2 : term230 A B t x h s) : (term329 A B h x'' x) = x.
Proof. exact (@lem5988834 A B x t x'' s h h1 (@lem5988785 A B t x h s h2)). Qed.
Lemma lem5988838 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term207 A B t x'' s h) (h2 : term230 A B t x h s) : term369 A B h x'' x.
Proof. exact (fun h0 : term370 A B h x'' x => @lem5988837 A B x'' t x h s h1 h2). Qed.
Lemma lem5988840 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5988841 {A B : Type'} (h : A -> B) (x'' : B -> A) (x : B) : (term369 A B h x'' x) = ((term329 A B h x'' x) = x).
Proof. exact (@lem5988840 ((term329 A B h x'' x) = x)). Qed.
Lemma lem5988842 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term207 A B t x'' s h) (h2 : term230 A B t x h s) : (term329 A B h x'' x) = x.
Proof. exact (EQ_MP (@lem5988841 A B h x'' x) (@lem5988838 A B x'' t x h s h1 h2)). Qed.
Lemma lem5988844 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5988845 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5988844 B x). Qed.
Lemma lem5988846 {A B : Type'} (h : A -> B) (x'' : B -> A) (x : B) : (term329 A B h x'' x) = (term329 A B h x'' x).
Proof. exact (@lem5988845 B (term329 A B h x'' x)). Qed.
Lemma lem5988847 {A B : Type'} (h : A -> B) (x'' : B -> A) (x : B) : term371 A B h x'' x.
Proof. exact (fun h0 : term372 A B h x'' x => @lem5988846 A B h x'' x). Qed.
Lemma lem5988849 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5988850 {A B : Type'} (h : A -> B) (x'' : B -> A) (x : B) : (term371 A B h x'' x) = ((term329 A B h x'' x) = (term329 A B h x'' x)).
Proof. exact (@lem5988849 ((term329 A B h x'' x) = (term329 A B h x'' x))). Qed.
Lemma lem5988851 {A B : Type'} (h : A -> B) (x'' : B -> A) (x : B) : (term329 A B h x'' x) = (term329 A B h x'' x).
Proof. exact (EQ_MP (@lem5988850 A B h x'' x) (@lem5988847 A B h x'' x)). Qed.
Lemma lem5988869 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5988870 {B : Type'} (y : B) (x : B) (z : B) : (term373 B x y z) = (term374 B y x z).
Proof. exact (@lem5988869 (y = z) (term375 B x z)). Qed.
Lemma lem5988880 {B : Type'} (x : B) (y : B) : (term376 B x y) = (term376 B x y).
Proof. exact (eq_refl (term376 B x y)). Qed.
Lemma lem5988881 {B : Type'} (y : B) (x : B) (z : B) : (term358 B x y z) = (term377 B y x z).
Proof. exact (MK_COMB (@lem5988880 B x y) (@lem5988870 B y x z)). Qed.
Lemma lem5988885 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5988886 {B : Type'} (y : B) (x : B) (z : B) : (term377 B y x z) = (term378 B y x z).
Proof. exact (@lem5988885 (y = z) (term375 B x y) (term375 B x z)). Qed.
Lemma lem5988908 {B : Type'} (y : B) (x : B) (z : B) : (term358 B x y z) = (term378 B y x z).
Proof. exact (TRANS (@lem5988881 B y x z) (@lem5988886 B y x z)). Qed.
Lemma lem5988909 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5988910 {B : Type'} (y : B) (x : B) (z : B) : (term379 B x y z) = (term380 B y x z).
Proof. exact (MK_COMB (@lem5988909) (@lem5988908 B y x z)). Qed.
Lemma lem5988932 {B : Type'} (y : B) (x : B) (z : B) : (term378 B y x z) = (term378 B y x z).
Proof. exact (eq_refl (term378 B y x z)). Qed.
Lemma lem5988933 {B : Type'} (y : B) (x : B) (z : B) : ((term358 B x y z) = (term378 B y x z)) = ((term378 B y x z) = (term378 B y x z)).
Proof. exact (MK_COMB (@lem5988910 B y x z) (@lem5988932 B y x z)). Qed.
Lemma lem5988935 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5988936 (x : Prop) : (x = x) = True.
Proof. exact (@lem5988935 Prop x). Qed.
Lemma lem5988937 {B : Type'} (y : B) (x : B) (z : B) : ((term378 B y x z) = (term378 B y x z)) = True.
Proof. exact (@lem5988936 (term378 B y x z)). Qed.
Lemma lem5988938 {B : Type'} (y : B) (x : B) (z : B) : ((term358 B x y z) = (term378 B y x z)) = True.
Proof. exact (TRANS (@lem5988933 B y x z) (@lem5988937 B y x z)). Qed.
Lemma lem5988939 {B : Type'} (y : B) (x : B) (z : B) : True = ((term358 B x y z) = (term378 B y x z)).
Proof. exact (SYM (@lem5988938 B y x z)). Qed.
Lemma lem5988940 {B : Type'} (y : B) (x : B) (z : B) : (term358 B x y z) = (term378 B y x z).
Proof. exact (EQ_MP (@lem5988939 B y x z) (@lem0)). Qed.
Lemma lem5988941 {B : Type'} (y : B) (x : B) (z : B) : term378 B y x z.
Proof. exact (EQ_MP (@lem5988940 B y x z) (@lem5988768 B x y z)). Qed.
Lemma lem5988943 (b : Prop) (a : Prop) : (a \/ b) = (term364 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5988944 {B : Type'} (x : B) (y : B) (z : B) : (term378 B y x z) = (term381 B x y z).
Proof. exact (@lem5988943 (term382 B y x z) (y = z)). Qed.
Lemma lem5988946 (a : Prop) (b : Prop) : (term383 a b) = (term384 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5988947 {B : Type'} (y : B) (x : B) (z : B) : (term385 B y x z) = (term386 B y x z).
Proof. exact (@lem5988946 (term375 B x y) (term375 B x z)). Qed.
Lemma lem5988949 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5988950 {B : Type'} (x : B) (y : B) : (term387 B x y) = (x = y).
Proof. exact (@lem5988949 (x = y)). Qed.
Lemma lem5988951 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5988952 {B : Type'} (x : B) (y : B) : (term388 B x y) = (term389 B x y).
Proof. exact (MK_COMB (@lem5988951) (@lem5988950 B x y)). Qed.
Lemma lem5988954 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5988955 {B : Type'} (x : B) (z : B) : (term387 B x z) = (x = z).
Proof. exact (@lem5988954 (x = z)). Qed.
Lemma lem5988956 {B : Type'} (y : B) (x : B) (z : B) : (term386 B y x z) = (term390 B y x z).
Proof. exact (MK_COMB (@lem5988952 B x y) (@lem5988955 B x z)). Qed.
Lemma lem5988957 {B : Type'} (y : B) (x : B) (z : B) : (term385 B y x z) = (term390 B y x z).
Proof. exact (TRANS (@lem5988947 B y x z) (@lem5988956 B y x z)). Qed.
Lemma lem5988958 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5988959 {B : Type'} (y : B) (x : B) (z : B) : (term391 B y x z) = (term392 B y x z).
Proof. exact (MK_COMB (@lem5988958) (@lem5988957 B y x z)). Qed.
Lemma lem5988960 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5988961 {B : Type'} (x : B) (y : B) (z : B) : (term381 B x y z) = (term393 B x y z).
Proof. exact (MK_COMB (@lem5988959 B y x z) (@lem5988960 B y z)). Qed.
Lemma lem5988962 {B : Type'} (x : B) (y : B) (z : B) : (term378 B y x z) = (term393 B x y z).
Proof. exact (TRANS (@lem5988944 B x y z) (@lem5988961 B x y z)). Qed.
Lemma lem5988964 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term207 A B t x'' s h) (h2 : term230 A B t x h s) : term394 A B h x'' x.
Proof. exact (conj (@lem5988842 A B x'' t x h s h1 h2) (@lem5988851 A B h x'' x)). Qed.
Lemma lem5988966 {B : Type'} (x : B) (y : B) (z : B) : term393 B x y z.
Proof. exact (EQ_MP (@lem5988962 B x y z) (@lem5988941 B y x z)). Qed.
Lemma lem5988967 {B : Type'} (x : B) (y : B) (z : B) : term393 B x y z.
Proof. exact (@lem5988966 B x y z). Qed.
Lemma lem5988968 {A B : Type'} (h : A -> B) (x'' : B -> A) (x : B) : term395 A B h x'' x.
Proof. exact (@lem5988967 B (term329 A B h x'' x) x (term329 A B h x'' x)). Qed.
Lemma lem5988971 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term207 A B t x'' s h) (h2 : term230 A B t x h s) : x = (term329 A B h x'' x).
Proof. exact (@lem5988968 A B h x'' x (@lem5988964 A B x'' t x h s h1 h2)). Qed.
Lemma lem5988972 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term207 A B t x'' s h) (h2 : term230 A B t x h s) : term396 A B h x'' x.
Proof. exact (fun h0 : term397 A B h x'' x => @lem5988971 A B x'' t x h s h1 h2). Qed.
Lemma lem5988974 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5988975 {A B : Type'} (h : A -> B) (x'' : B -> A) (x : B) : (term396 A B h x'' x) = (x = (term329 A B h x'' x)).
Proof. exact (@lem5988974 (x = (term329 A B h x'' x))). Qed.
Lemma lem5988976 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term207 A B t x'' s h) (h2 : term230 A B t x h s) : x = (term329 A B h x'' x).
Proof. exact (EQ_MP (@lem5988975 A B h x'' x) (@lem5988972 A B x'' t x h s h1 h2)). Qed.
Lemma lem5988978 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term230 A B t x h s) : @IN B x t.
Proof. exact (proj1 (@lem5987948 A B t x h s h1)). Qed.
Lemma lem5988979 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term230 A B t x h s) : term359 B x t.
Proof. exact (fun h0 : term173 B x t => @lem5988978 A B t x h s h1). Qed.
Lemma lem5988981 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5988982 {B : Type'} (x : B) (t : B -> Prop) : (term359 B x t) = (@IN B x t).
Proof. exact (@lem5988981 (@IN B x t)). Qed.
Lemma lem5988983 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term230 A B t x h s) : @IN B x t.
Proof. exact (EQ_MP (@lem5988982 B x t) (@lem5988979 A B t x h s h1)). Qed.
Lemma lem5988989 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5988990 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (_76047 : B) (t : B -> Prop) : (term349 A B t x'' _76047 s) = (term398 A B x'' s _76047 t).
Proof. exact (@lem5988989 (term328 A B x'' _76047 s) (term173 B _76047 t)). Qed.
Lemma lem5988996 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5988997 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (_76047 : B) (t : B -> Prop) : (term399 A B t x'' _76047 s) = (term400 A B x'' s _76047 t).
Proof. exact (MK_COMB (@lem5988996) (@lem5988990 A B x'' s _76047 t)). Qed.
Lemma lem5989003 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (_76047 : B) (t : B -> Prop) : (term398 A B x'' s _76047 t) = (term398 A B x'' s _76047 t).
Proof. exact (eq_refl (term398 A B x'' s _76047 t)). Qed.
Lemma lem5989004 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (_76047 : B) (t : B -> Prop) : ((term349 A B t x'' _76047 s) = (term398 A B x'' s _76047 t)) = ((term398 A B x'' s _76047 t) = (term398 A B x'' s _76047 t)).
Proof. exact (MK_COMB (@lem5988997 A B x'' s _76047 t) (@lem5989003 A B x'' s _76047 t)). Qed.
Lemma lem5989006 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5989007 (x : Prop) : (x = x) = True.
Proof. exact (@lem5989006 Prop x). Qed.
Lemma lem5989008 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (_76047 : B) (t : B -> Prop) : ((term398 A B x'' s _76047 t) = (term398 A B x'' s _76047 t)) = True.
Proof. exact (@lem5989007 (term398 A B x'' s _76047 t)). Qed.
Lemma lem5989009 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (_76047 : B) (t : B -> Prop) : ((term349 A B t x'' _76047 s) = (term398 A B x'' s _76047 t)) = True.
Proof. exact (TRANS (@lem5989004 A B x'' s _76047 t) (@lem5989008 A B x'' s _76047 t)). Qed.
Lemma lem5989010 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (_76047 : B) (t : B -> Prop) : True = ((term349 A B t x'' _76047 s) = (term398 A B x'' s _76047 t)).
Proof. exact (SYM (@lem5989009 A B x'' s _76047 t)). Qed.
Lemma lem5989011 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (_76047 : B) (t : B -> Prop) : (term349 A B t x'' _76047 s) = (term398 A B x'' s _76047 t).
Proof. exact (EQ_MP (@lem5989010 A B x'' s _76047 t) (@lem0)). Qed.
Lemma lem5989012 {A B : Type'} (_76047 : B) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x'' s h) : term398 A B x'' s _76047 t.
Proof. exact (EQ_MP (@lem5989011 A B x'' s _76047 t) (@lem5988483 A B _76047 t x'' s h h1)). Qed.
Lemma lem5989014 (b : Prop) (a : Prop) : (a \/ b) = (term364 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5989015 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (_76047 : B) (s : A -> Prop) : (term398 A B x'' s _76047 t) = (term401 A B t x'' _76047 s).
Proof. exact (@lem5989014 (term173 B _76047 t) (term328 A B x'' _76047 s)). Qed.
Lemma lem5989017 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5989018 {B : Type'} (_76047 : B) (t : B -> Prop) : (term366 B _76047 t) = (@IN B _76047 t).
Proof. exact (@lem5989017 (@IN B _76047 t)). Qed.
Lemma lem5989019 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5989020 {B : Type'} (_76047 : B) (t : B -> Prop) : (term367 B _76047 t) = (term99 B _76047 t).
Proof. exact (MK_COMB (@lem5989019) (@lem5989018 B _76047 t)). Qed.
Lemma lem5989021 {A B : Type'} (x'' : B -> A) (_76047 : B) (s : A -> Prop) : (term328 A B x'' _76047 s) = (term328 A B x'' _76047 s).
Proof. exact (eq_refl (term328 A B x'' _76047 s)). Qed.
Lemma lem5989022 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (_76047 : B) (s : A -> Prop) : (term401 A B t x'' _76047 s) = (term402 A B t x'' _76047 s).
Proof. exact (MK_COMB (@lem5989020 B _76047 t) (@lem5989021 A B x'' _76047 s)). Qed.
Lemma lem5989023 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (_76047 : B) (s : A -> Prop) : (term398 A B x'' s _76047 t) = (term402 A B t x'' _76047 s).
Proof. exact (TRANS (@lem5989015 A B t x'' _76047 s) (@lem5989022 A B t x'' _76047 s)). Qed.
Lemma lem5989026 {A B : Type'} (_76047 : B) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x'' s h) : term402 A B t x'' _76047 s.
Proof. exact (EQ_MP (@lem5989023 A B t x'' _76047 s) (@lem5989012 A B _76047 t x'' s h h1)). Qed.
Lemma lem5989027 {A B : Type'} (_76047 : B) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x'' s h) : term402 A B t x'' _76047 s.
Proof. exact (@lem5989026 A B _76047 t x'' s h h1). Qed.
Lemma lem5989028 {A B : Type'} (x : B) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x'' s h) : term402 A B t x'' x s.
Proof. exact (@lem5989027 A B x t x'' s h h1). Qed.
Lemma lem5989031 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term207 A B t x'' s h) (h2 : term230 A B t x h s) : term328 A B x'' x s.
Proof. exact (@lem5989028 A B x t x'' s h h1 (@lem5988983 A B t x h s h2)). Qed.
Lemma lem5989032 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term207 A B t x'' s h) (h2 : term230 A B t x h s) : term403 A B x'' x s.
Proof. exact (fun h0 : term404 A B x'' x s => @lem5989031 A B x'' t x h s h1 h2). Qed.
Lemma lem5989034 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5989035 {A B : Type'} (x'' : B -> A) (x : B) (s : A -> Prop) : (term403 A B x'' x s) = (term328 A B x'' x s).
Proof. exact (@lem5989034 (term328 A B x'' x s)). Qed.
Lemma lem5989036 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term207 A B t x'' s h) (h2 : term230 A B t x h s) : term328 A B x'' x s.
Proof. exact (EQ_MP (@lem5989035 A B x'' x s) (@lem5989032 A B x'' t x h s h1 h2)). Qed.
Lemma lem5989038 (a : Prop) (b : Prop) : (term405 a b) = (term406 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5989039 {A B : Type'} (x : B) (h : A -> B) (_76050 : A) (s : A -> Prop) : (term216 A B x h _76050 s) = (term215 A B x h _76050 s).
Proof. exact (@lem5989038 (x = (h _76050)) (@IN A _76050 s)). Qed.
Lemma lem5989041 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5989042 {A B : Type'} (x : B) (h : A -> B) (_76050 : A) (s : A -> Prop) : (term215 A B x h _76050 s) = (term407 A B x h _76050 s).
Proof. exact (@lem5989041 (term92 A B x h _76050 s)). Qed.
Lemma lem5989043 {A B : Type'} (x : B) (h : A -> B) (_76050 : A) (s : A -> Prop) : (term216 A B x h _76050 s) = (term407 A B x h _76050 s).
Proof. exact (TRANS (@lem5989039 A B x h _76050 s) (@lem5989042 A B x h _76050 s)). Qed.
Lemma lem5989045 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term207 A B t x'' s h) (h2 : term230 A B t x h s) : term408 A B h x'' x s.
Proof. exact (conj (@lem5988976 A B x'' t x h s h1 h2) (@lem5989036 A B x'' t x h s h1 h2)). Qed.
Lemma lem5989047 {A B : Type'} (_76050 : A) (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term230 A B t x h s) : term407 A B x h _76050 s.
Proof. exact (EQ_MP (@lem5989043 A B x h _76050 s) (@lem5988451 A B _76050 t x h s h1)). Qed.
Lemma lem5989048 {A B : Type'} (_76050 : A) (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term230 A B t x h s) : term407 A B x h _76050 s.
Proof. exact (@lem5989047 A B _76050 t x h s h1). Qed.
Lemma lem5989049 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term230 A B t x h s) : term409 A B h x'' x s.
Proof. exact (@lem5989048 A B (x'' x) t x h s h1). Qed.
Lemma lem5989052 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term207 A B t x'' s h) (h2 : term230 A B t x h s) : False.
Proof. exact (@lem5989049 A B x'' t x h s h2 (@lem5989045 A B x'' t x h s h1 h2)). Qed.
Lemma lem5989053 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term207 A B t x'' s h) (h2 : term230 A B t x h s) : term410.
Proof. exact (fun h0 : ~ False => @lem5989052 A B x'' t x h s h1 h2). Qed.
Lemma lem5989055 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5989056 : term410 = False.
Proof. exact (@lem5989055 False). Qed.
Lemma lem5989057 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term207 A B t x'' s h) (h2 : term230 A B t x h s) : False.
Proof. exact (EQ_MP (@lem5989056) (@lem5989053 A B x'' t x h s h1 h2)). Qed.
Lemma lem5989153 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) (h1 : term244 A B t x h x' s) : @IN A x' s.
Proof. exact (proj2 (@lem5987952 A B t x h x' s h1)). Qed.
Lemma lem5989154 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) (h1 : term244 A B t x h x' s) : term359 A x' s.
Proof. exact (fun h0 : term173 A x' s => @lem5989153 A B t x h x' s h1). Qed.
Lemma lem5989156 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5989157 {A : Type'} (x' : A) (s : A -> Prop) : (term359 A x' s) = (@IN A x' s).
Proof. exact (@lem5989156 (@IN A x' s)). Qed.
Lemma lem5989158 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) (h1 : term244 A B t x h x' s) : @IN A x' s.
Proof. exact (EQ_MP (@lem5989157 A x' s) (@lem5989154 A B t x h x' s h1)). Qed.
Lemma lem5989164 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5989165 {A B : Type'} (h : A -> B) (t : B -> Prop) (_76051 : A) (s : A -> Prop) : (term357 A B s h _76051 t) = (term411 A B h t _76051 s).
Proof. exact (@lem5989164 (term340 A B h _76051 t) (term173 A _76051 s)). Qed.
Lemma lem5989171 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5989172 {A B : Type'} (h : A -> B) (t : B -> Prop) (_76051 : A) (s : A -> Prop) : (term412 A B s h _76051 t) = (term413 A B h t _76051 s).
Proof. exact (MK_COMB (@lem5989171) (@lem5989165 A B h t _76051 s)). Qed.
Lemma lem5989178 {A B : Type'} (h : A -> B) (t : B -> Prop) (_76051 : A) (s : A -> Prop) : (term411 A B h t _76051 s) = (term411 A B h t _76051 s).
Proof. exact (eq_refl (term411 A B h t _76051 s)). Qed.
Lemma lem5989179 {A B : Type'} (h : A -> B) (t : B -> Prop) (_76051 : A) (s : A -> Prop) : ((term357 A B s h _76051 t) = (term411 A B h t _76051 s)) = ((term411 A B h t _76051 s) = (term411 A B h t _76051 s)).
Proof. exact (MK_COMB (@lem5989172 A B h t _76051 s) (@lem5989178 A B h t _76051 s)). Qed.
Lemma lem5989181 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5989182 (x : Prop) : (x = x) = True.
Proof. exact (@lem5989181 Prop x). Qed.
Lemma lem5989183 {A B : Type'} (h : A -> B) (t : B -> Prop) (_76051 : A) (s : A -> Prop) : ((term411 A B h t _76051 s) = (term411 A B h t _76051 s)) = True.
Proof. exact (@lem5989182 (term411 A B h t _76051 s)). Qed.
Lemma lem5989184 {A B : Type'} (h : A -> B) (t : B -> Prop) (_76051 : A) (s : A -> Prop) : ((term357 A B s h _76051 t) = (term411 A B h t _76051 s)) = True.
Proof. exact (TRANS (@lem5989179 A B h t _76051 s) (@lem5989183 A B h t _76051 s)). Qed.
Lemma lem5989185 {A B : Type'} (h : A -> B) (t : B -> Prop) (_76051 : A) (s : A -> Prop) : True = ((term357 A B s h _76051 t) = (term411 A B h t _76051 s)).
Proof. exact (SYM (@lem5989184 A B h t _76051 s)). Qed.
Lemma lem5989186 {A B : Type'} (h : A -> B) (t : B -> Prop) (_76051 : A) (s : A -> Prop) : (term357 A B s h _76051 t) = (term411 A B h t _76051 s).
Proof. exact (EQ_MP (@lem5989185 A B h t _76051 s) (@lem0)). Qed.
Lemma lem5989187 {A B C : Type'} (_76051 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term411 A B h t _76051 s.
Proof. exact (EQ_MP (@lem5989186 A B h t _76051 s) (@lem5988670 A B C _76051 s t g h f h1)). Qed.
Lemma lem5989189 (b : Prop) (a : Prop) : (a \/ b) = (term364 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5989190 {A B : Type'} (s : A -> Prop) (h : A -> B) (_76051 : A) (t : B -> Prop) : (term411 A B h t _76051 s) = (term414 A B s h _76051 t).
Proof. exact (@lem5989189 (term173 A _76051 s) (term340 A B h _76051 t)). Qed.
Lemma lem5989192 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5989193 {A : Type'} (_76051 : A) (s : A -> Prop) : (term366 A _76051 s) = (@IN A _76051 s).
Proof. exact (@lem5989192 (@IN A _76051 s)). Qed.
Lemma lem5989194 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5989195 {A : Type'} (_76051 : A) (s : A -> Prop) : (term367 A _76051 s) = (term99 A _76051 s).
Proof. exact (MK_COMB (@lem5989194) (@lem5989193 A _76051 s)). Qed.
Lemma lem5989196 {A B : Type'} (h : A -> B) (_76051 : A) (t : B -> Prop) : (term340 A B h _76051 t) = (term340 A B h _76051 t).
Proof. exact (eq_refl (term340 A B h _76051 t)). Qed.
Lemma lem5989197 {A B : Type'} (s : A -> Prop) (h : A -> B) (_76051 : A) (t : B -> Prop) : (term414 A B s h _76051 t) = (term415 A B s h _76051 t).
Proof. exact (MK_COMB (@lem5989195 A _76051 s) (@lem5989196 A B h _76051 t)). Qed.
Lemma lem5989198 {A B : Type'} (s : A -> Prop) (h : A -> B) (_76051 : A) (t : B -> Prop) : (term411 A B h t _76051 s) = (term415 A B s h _76051 t).
Proof. exact (TRANS (@lem5989190 A B s h _76051 t) (@lem5989197 A B s h _76051 t)). Qed.
Lemma lem5989201 {A B C : Type'} (_76051 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term415 A B s h _76051 t.
Proof. exact (EQ_MP (@lem5989198 A B s h _76051 t) (@lem5989187 A B C _76051 s t g h f h1)). Qed.
Lemma lem5989202 {A B C : Type'} (_76051 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term415 A B s h _76051 t.
Proof. exact (@lem5989201 A B C _76051 s t g h f h1). Qed.
Lemma lem5989203 {A B C : Type'} (x' : A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term415 A B s h x' t.
Proof. exact (@lem5989202 A B C x' s t g h f h1). Qed.
Lemma lem5989206 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) (h1 : term38 A B C s t g h f) (h2 : term244 A B t x h x' s) : term340 A B h x' t.
Proof. exact (@lem5989203 A B C x' s t g h f h1 (@lem5989158 A B t x h x' s h2)). Qed.
Lemma lem5989207 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) (h1 : term38 A B C s t g h f) (h2 : term244 A B t x h x' s) : term416 A B h x' t.
Proof. exact (fun h0 : term354 A B h x' t => @lem5989206 A B C g f t x h x' s h1 h2). Qed.
Lemma lem5989209 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5989210 {A B : Type'} (h : A -> B) (x' : A) (t : B -> Prop) : (term416 A B h x' t) = (term340 A B h x' t).
Proof. exact (@lem5989209 (term340 A B h x' t)). Qed.
Lemma lem5989211 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) (h1 : term38 A B C s t g h f) (h2 : term244 A B t x h x' s) : term340 A B h x' t.
Proof. exact (EQ_MP (@lem5989210 A B h x' t) (@lem5989207 A B C g f t x h x' s h1 h2)). Qed.
Lemma lem5989214 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5989216 {A B : Type'} (h : A -> B) (x' : A) (t : B -> Prop) : (term354 A B h x' t) = (term417 A B h x' t).
Proof. exact (@lem5989214 (term340 A B h x' t)). Qed.
Lemma lem5989219 {A B : Type'} (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) (h1 : term244 A B t x h x' s) : term417 A B h x' t.
Proof. exact (EQ_MP (@lem5989216 A B h x' t) (@lem5988600 A B t x h x' s h1)). Qed.
Lemma lem5989222 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) (h1 : term38 A B C s t g h f) (h2 : term244 A B t x h x' s) : False.
Proof. exact (@lem5989219 A B t x h x' s h2 (@lem5989211 A B C g f t x h x' s h1 h2)). Qed.
Lemma lem5989223 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) (h1 : term38 A B C s t g h f) (h2 : term244 A B t x h x' s) : term410.
Proof. exact (fun h0 : ~ False => @lem5989222 A B C g f t x h x' s h1 h2). Qed.
Lemma lem5989225 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5989226 : term410 = False.
Proof. exact (@lem5989225 False). Qed.
Lemma lem5989228 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) (h1 : term38 A B C s t g h f) (h2 : term244 A B t x h x' s) : False.
Proof. exact (EQ_MP (@lem5989226) (@lem5989223 A B C g f t x h x' s h1 h2)). Qed.
Lemma lem5989229 {A B C : Type'} (g : B -> C) (f : A -> C) (x'' : B -> A) (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) (h1 : term38 A B C s t g h f) (h2 : term207 A B t x'' s h) (h3 : term257 A B t x h x' s) : False.
Proof. exact (or_elim (@lem5987856 A B t x h x' s h3) (fun h0 : term230 A B t x h s => @lem5989057 A B x'' t x h s h2 h0) (fun h0 : term244 A B t x h x' s => @lem5989228 A B C g f t x h x' s h1 h0)). Qed.
Lemma lem5989230 {A B C : Type'} (g : B -> C) (f : A -> C) (x'' : B -> A) (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) (h1 : term38 A B C s t g h f) (h2 : term207 A B t x'' s h) (h3 : term257 A B t x h x' s) : (term207 A B t x'' s h) = False.
Proof. exact (prop_ext (fun h4 : term207 A B t x'' s h => @lem5989229 A B C g f x'' t x h x' s h1 h2 h3) (fun h4 : False => @lem5987947 A B t x'' s h h2)). Qed.
Lemma lem5989231 {A B C : Type'} (g : B -> C) (f : A -> C) (x'' : B -> A) (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) (h1 : term38 A B C s t g h f) (h2 : term207 A B t x'' s h) (h3 : term257 A B t x h x' s) : False.
Proof. exact (EQ_MP (@lem5989230 A B C g f x'' t x h x' s h1 h2 h3) (@lem5987947 A B t x'' s h h2)). Qed.
Lemma lem5989232 {A B C : Type'} (g : B -> C) (f : A -> C) (x'' : B -> A) (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) (h1 : term38 A B C s t g h f) (h2 : term207 A B t x'' s h) (h3 : term257 A B t x h x' s) : (term257 A B t x h x' s) = False.
Proof. exact (prop_ext (fun h4 : term257 A B t x h x' s => @lem5989231 A B C g f x'' t x h x' s h1 h2 h3) (fun h4 : False => @lem5987856 A B t x h x' s h3)). Qed.
Lemma lem5989233 {A B C : Type'} (g : B -> C) (f : A -> C) (x'' : B -> A) (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) (h1 : term38 A B C s t g h f) (h2 : term207 A B t x'' s h) (h3 : term257 A B t x h x' s) : False.
Proof. exact (EQ_MP (@lem5989232 A B C g f x'' t x h x' s h1 h2 h3) (@lem5987856 A B t x h x' s h3)). Qed.
Lemma lem5989234 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (x : B) (h : A -> B) (x' : A) (s : A -> Prop) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term257 A B t x h x' s) : False.
Proof. exact (ex_elim (@lem5987508 A B t s h h2) (fun x'' : B -> A => fun h0 : term209 A B t s h x'' => @lem5989233 A B C g f x'' t x h x' s h1 h0 h3)). Qed.
Lemma lem5989235 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term103 A B t x h s) : False.
Proof. exact (ex_elim (@lem5987756 A B t x h s h3) (fun x' : A => fun h0 : term259 A B t x h s x' => @lem5989234 A B C g f t x h x' s h1 h2 h0)). Qed.
Lemma lem5989236 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term103 A B t x h s) : (term103 A B t x h s) = False.
Proof. exact (prop_ext (fun h4 : term103 A B t x h s => @lem5989235 A B C g f t x h s h1 h2 h3) (fun h4 : False => @lem5987090 A B t x h s h3)). Qed.
Lemma lem5989237 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (x : B) (h : A -> B) (s : A -> Prop) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term103 A B t x h s) : False.
Proof. exact (EQ_MP (@lem5989236 A B C g f t x h s h1 h2 h3) (@lem5987090 A B t x h s h3)). Qed.
Lemma lem5989238 {A B C : Type'} (x : B) (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) : term102 A B t x h s.
Proof. exact (fun h0 : term103 A B t x h s => @lem5989237 A B C g f t x h s h1 h2 h0). Qed.
Lemma lem5989239 {A B C : Type'} (x : B) (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) : (@IN B x t) = (term32 A B x h s).
Proof. exact (EQ_MP (@lem5987089 A B t x h s) (@lem5989238 A B C x g f t s h h1 h2)). Qed.
Lemma lem5989244 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) : term50 A B t h s.
Proof. exact (fun x : B => @lem5989239 A B C x g f t s h h1 h2). Qed.
Lemma lem5989245 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (h1 : term39 A B t s h) : term62 A B C g f t h s.
Proof. exact (fun h0 : term38 A B C s t g h f => @lem5989244 A B C g f t s h h0 h1). Qed.
Lemma lem5989246 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : term65 A B C g f t h s.
Proof. exact (fun h0 : term39 A B t s h => @lem5989245 A B C g f t s h h0). Qed.
Lemma lem5989247 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : term67 A B C op g f t h s.
Proof. exact (fun h0 : @monoidal C op => @lem5989246 A B C g f t h s). Qed.
Lemma lem5989252 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : term71 A B C g f t h s.
Proof. exact (fun op : type1400 C => @lem5989247 A B C op g f t h s). Qed.
Lemma lem5989257 {A B C : Type'} (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : term75 A B C f t h s.
Proof. exact (fun g : B -> C => @lem5989252 A B C g f t h s). Qed.
Lemma lem5989262 {A B C : Type'} (t : B -> Prop) (h : A -> B) (s : A -> Prop) : term79 A B C t h s.
Proof. exact (fun f : A -> C => @lem5989257 A B C f t h s). Qed.
Lemma lem5989267 {A B C : Type'} (h : A -> B) (s : A -> Prop) : term83 A B C h s.
Proof. exact (fun t : B -> Prop => @lem5989262 A B C t h s). Qed.
Lemma lem5989272 {A B C : Type'} (s : A -> Prop) : term87 A B C s.
Proof. exact (fun h : A -> B => @lem5989267 A B C h s). Qed.
Lemma lem5989277 {A B C : Type'} : term91 A B C.
Proof. exact (fun s : A -> Prop => @lem5989272 A B C s). Qed.
Lemma lem5989278 {A B C : Type'} : term90 A B C.
Proof. exact (EQ_MP (@lem5987082 A B C) (@lem5989277 A B C)). Qed.
Lemma lem5989279 {A B C : Type'} (s : A -> Prop) : term418 A B C s.
Proof. exact (@lem5989278 A B C s). Qed.
Lemma lem5989280 {A B C : Type'} (s : A -> Prop) : (term418 A B C s) = (term86 A B C s).
Proof. exact (eq_refl (term418 A B C s)). Qed.
Lemma lem5989281 {A B C : Type'} (s : A -> Prop) : term86 A B C s.
Proof. exact (EQ_MP (@lem5989280 A B C s) (@lem5989279 A B C s)). Qed.
Lemma lem5989282 {A B C : Type'} (s : A -> Prop) (h : A -> B) : term419 A B C s h.
Proof. exact (@lem5989281 A B C s h). Qed.
Lemma lem5989283 {A B C : Type'} (h : A -> B) (s : A -> Prop) : (term419 A B C s h) = (term82 A B C h s).
Proof. exact (eq_refl (term419 A B C s h)). Qed.
Lemma lem5989284 {A B C : Type'} (h : A -> B) (s : A -> Prop) : term82 A B C h s.
Proof. exact (EQ_MP (@lem5989283 A B C h s) (@lem5989282 A B C s h)). Qed.
Lemma lem5989285 {A B C : Type'} (h : A -> B) (s : A -> Prop) (t : B -> Prop) : term420 A B C h s t.
Proof. exact (@lem5989284 A B C h s t). Qed.
Lemma lem5989286 {A B C : Type'} (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term420 A B C h s t) = (term78 A B C t h s).
Proof. exact (eq_refl (term420 A B C h s t)). Qed.
Lemma lem5989287 {A B C : Type'} (t : B -> Prop) (h : A -> B) (s : A -> Prop) : term78 A B C t h s.
Proof. exact (EQ_MP (@lem5989286 A B C t h s) (@lem5989285 A B C h s t)). Qed.
Lemma lem5989288 {A B C : Type'} (t : B -> Prop) (h : A -> B) (s : A -> Prop) (f : A -> C) : term421 A B C t h s f.
Proof. exact (@lem5989287 A B C t h s f). Qed.
Lemma lem5989289 {A B C : Type'} (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term421 A B C t h s f) = (term74 A B C f t h s).
Proof. exact (eq_refl (term421 A B C t h s f)). Qed.
Lemma lem5989290 {A B C : Type'} (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : term74 A B C f t h s.
Proof. exact (EQ_MP (@lem5989289 A B C f t h s) (@lem5989288 A B C t h s f)). Qed.
Lemma lem5989291 {A B C : Type'} (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) (g : B -> C) : term422 A B C f t h s g.
Proof. exact (@lem5989290 A B C f t h s g). Qed.
Lemma lem5989292 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term422 A B C f t h s g) = (term70 A B C g f t h s).
Proof. exact (eq_refl (term422 A B C f t h s g)). Qed.
Lemma lem5989293 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : term70 A B C g f t h s.
Proof. exact (EQ_MP (@lem5989292 A B C g f t h s) (@lem5989291 A B C f t h s g)). Qed.
Lemma lem5989294 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) (op : type1400 C) : term423 A B C g f t h s op.
Proof. exact (@lem5989293 A B C g f t h s op). Qed.
Lemma lem5989295 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : (term423 A B C g f t h s op) = (term54 A B C op g f t h s).
Proof. exact (eq_refl (term423 A B C g f t h s op)). Qed.
Lemma lem5989296 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : term54 A B C op g f t h s.
Proof. exact (EQ_MP (@lem5989295 A B C op g f t h s) (@lem5989294 A B C g f t h s op)). Qed.
Lemma lem5989298 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) : term54 A B C op g f t h s.
Proof. exact (@lem5986767 A B C op g f t h s (@lem5989296 A B C op g f t h s)). Qed.
Lemma lem5989299 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) (op : type1400 C) (h1 : @monoidal C op) : term64 A B C g f t h s.
Proof. exact (@lem5989298 A B C op g f t h s (@lem5986686 C op h1)). Qed.
Lemma lem5989300 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (op : type1400 C) (h1 : term39 A B t s h) (h2 : @monoidal C op) : term61 A B C g f t h s.
Proof. exact (@lem5989299 A B C g f t h s op h2 (@lem5986689 A B t s h h1)). Qed.
Lemma lem5989301 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (op : type1400 C) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) : term52 A B t h s.
Proof. exact (@lem5989300 A B C g f t s h op h2 h3 (@lem5986688 A B C s t g h f h1)). Qed.
Lemma lem5989302 {A B C : Type'} (g : B -> C) (f : A -> C) (op : type1400 C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) (h4 : term53 A B t h s) : False.
Proof. exact (@lem5989301 A B C g f t s h op h1 h2 h3 (@lem5986751 A B t h s h4)). Qed.
Lemma lem5989303 {A B C : Type'} (g : B -> C) (f : A -> C) (op : type1400 C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) (h4 : term53 A B t h s) : (term53 A B t h s) = False.
Proof. exact (prop_ext (fun h5 : term53 A B t h s => @lem5989302 A B C g f op t h s h1 h2 h3 h4) (fun h5 : False => @lem5986751 A B t h s h4)). Qed.
Lemma lem5989304 {A B C : Type'} (g : B -> C) (f : A -> C) (op : type1400 C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) (h4 : term53 A B t h s) : False.
Proof. exact (EQ_MP (@lem5989303 A B C g f op t h s h1 h2 h3 h4) (@lem5986751 A B t h s h4)). Qed.
Lemma lem5989305 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (op : type1400 C) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) : term52 A B t h s.
Proof. exact (fun h0 : term53 A B t h s => @lem5989304 A B C g f op t h s h1 h2 h3 h0). Qed.
Lemma lem5989306 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (op : type1400 C) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) : term50 A B t h s.
Proof. exact (EQ_MP (@lem5986750 A B t h s) (@lem5989305 A B C g f t s h op h1 h2 h3)). Qed.
Lemma lem5989307 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (op : type1400 C) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) : t = (@IMAGE A B h s).
Proof. exact (EQ_MP (@lem5986746 A B t h s) (@lem5989306 A B C g f t s h op h1 h2 h3)). Qed.
Lemma lem5989309 {A : Type'} (x : A) (z : A) : term20 A x z.
Proof. exact (EQ_MP (@lem5986659 A x z) (@lem5986658 A x z)). Qed.
Lemma lem5989310 {C : Type'} (x : C) (z : C) : term20 C x z.
Proof. exact (@lem5989309 C x z). Qed.
Lemma lem5989311 {A B C : Type'} (f : A -> C) (op : type1400 C) (h : A -> B) (s : A -> Prop) (g : B -> C) : term424 A B C f op h s g.
Proof. exact (@lem5989310 C (@iterate C A op s f) (term43 A B C op h s g)). Qed.
Lemma lem5989313 (p : Prop) : p = (term51 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5989314 {A B C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : ((@iterate C A op s f) = (term425 A B C op s g h)) = (term426 A B C f op s g h).
Proof. exact (@lem5989313 ((@iterate C A op s f) = (term425 A B C op s g h))). Qed.
Lemma lem5989315 {A B C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term426 A B C f op s g h) = ((@iterate C A op s f) = (term425 A B C op s g h)).
Proof. exact (SYM (@lem5989314 A B C f op s g h)). Qed.
Lemma lem5989316 {A B C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term427 A B C f op s g h) : term427 A B C f op s g h.
Proof. exact (h1). Qed.
Lemma lem5989317 {A C : Type'} : term428 A C.
Proof. exact (@lem5985778 A C). Qed.
Lemma lem5989318 {B : Type'} : term429 B.
Proof. exact (@lem5985778 B B). Qed.
Lemma lem5989319 {A B : Type'} : term428 A B.
Proof. exact (@lem5985778 A B). Qed.
Lemma lem5989323 {A B : Type'} : term430 A B.
Proof. exact (@lem15456 A B B). Qed.
Lemma lem5989324 {A B C : Type'} : term431 A B C.
Proof. exact (@lem15456 A B C). Qed.
Lemma lem5989328 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term432 A B C t f op s g h) : term432 A B C t f op s g h.
Proof. exact (h1). Qed.
Lemma lem5989329 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : term433 A B C t f op s g h.
Proof. exact (fun h0 : term432 A B C t f op s g h => @lem5989328 A B C t f op s g h h0). Qed.
Lemma lem5989330 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term433 A B C t f op s g h) : term433 A B C t f op s g h.
Proof. exact (h1). Qed.
Lemma lem5989331 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term432 A B C t f op s g h) : term432 A B C t f op s g h.
Proof. exact (h1). Qed.
Lemma lem5989332 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term432 A B C t f op s g h) (h2 : term433 A B C t f op s g h) : term432 A B C t f op s g h.
Proof. exact (@lem5989330 A B C t f op s g h h2 (@lem5989331 A B C t f op s g h h1)). Qed.
Lemma lem5989333 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term432 A B C t f op s g h) : term434 A B C t f op s g h.
Proof. exact (fun h0 : term433 A B C t f op s g h => @lem5989332 A B C t f op s g h h1 h0). Qed.
Lemma lem5989334 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term433 A B C t f op s g h) : term433 A B C t f op s g h.
Proof. exact (h1). Qed.
Lemma lem5989335 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term432 A B C t f op s g h) (h2 : term433 A B C t f op s g h) : term432 A B C t f op s g h.
Proof. exact (@lem5989333 A B C t f op s g h h1 (@lem5989334 A B C t f op s g h h2)). Qed.
Lemma lem5989336 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term433 A B C t f op s g h) : term433 A B C t f op s g h.
Proof. exact (fun h0 : term432 A B C t f op s g h => @lem5989335 A B C t f op s g h h0 h1). Qed.
Lemma lem5989337 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : term435 A B C t f op s g h.
Proof. exact (fun h0 : term433 A B C t f op s g h => @lem5989336 A B C t f op s g h h0). Qed.
Lemma lem5989340 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : term433 A B C t f op s g h.
Proof. exact (@lem5989337 A B C t f op s g h (@lem5989329 A B C t f op s g h)). Qed.
Lemma lem5989341 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : term433 A B C t f op s g h.
Proof. exact (@lem5989340 A B C t f op s g h). Qed.
Lemma lem5989475 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5989476 {A C : Type'} : (term436 A C) = (term437 A C).
Proof. exact (@lem5989475 (term428 A C)). Qed.
Lemma lem5989503 {B : Type'} : (term438 B) = (term438 B).
Proof. exact (eq_refl (term438 B)). Qed.
Lemma lem5989504 {A B C : Type'} : (term439 A B C) = (term440 A B C).
Proof. exact (MK_COMB (@lem5989503 B) (@lem5989476 A C)). Qed.
Lemma lem5989507 {A B : Type'} : (term441 A B) = (term441 A B).
Proof. exact (eq_refl (term441 A B)). Qed.
Lemma lem5989508 {A B C : Type'} : (term442 A B C) = (term443 A B C).
Proof. exact (MK_COMB (@lem5989507 A B) (@lem5989504 A B C)). Qed.
Lemma lem5989511 {A B C : Type'} : (term444 A B C) = (term444 A B C).
Proof. exact (eq_refl (term444 A B C)). Qed.
Lemma lem5989512 {A B C : Type'} : (term445 A B C) = (term446 A B C).
Proof. exact (MK_COMB (@lem5989511 A B C) (@lem5989508 A B C)). Qed.
Lemma lem5989515 {A B : Type'} : (term447 A B) = (term447 A B).
Proof. exact (eq_refl (term447 A B)). Qed.
Lemma lem5989516 {A B C : Type'} : (term448 A B C) = (term449 A B C).
Proof. exact (MK_COMB (@lem5989515 A B) (@lem5989512 A B C)). Qed.
Lemma lem5989519 {A B C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term450 A B C f op s g h) = (term450 A B C f op s g h).
Proof. exact (eq_refl (term450 A B C f op s g h)). Qed.
Lemma lem5989520 {A B C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term451 A B C f op s g h) = (term452 A B C f op s g h).
Proof. exact (MK_COMB (@lem5989519 A B C f op s g h) (@lem5989516 A B C)). Qed.
Lemma lem5989523 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term60 A B C s t g h f) = (term60 A B C s t g h f).
Proof. exact (eq_refl (term60 A B C s t g h f)). Qed.
Lemma lem5989524 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term453 A B C t f op s g h) = (term454 A B C t f op s g h).
Proof. exact (MK_COMB (@lem5989523 A B C s t g h f) (@lem5989520 A B C f op s g h)). Qed.
Lemma lem5989527 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term63 A B t s h) = (term63 A B t s h).
Proof. exact (eq_refl (term63 A B t s h)). Qed.
Lemma lem5989528 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term455 A B C t f op s g h) = (term456 A B C t f op s g h).
Proof. exact (MK_COMB (@lem5989527 A B t s h) (@lem5989524 A B C t f op s g h)). Qed.
Lemma lem5989531 {C : Type'} (op : type1400 C) : (term66 C op) = (term66 C op).
Proof. exact (eq_refl (term66 C op)). Qed.
Lemma lem5989532 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term432 A B C t f op s g h) = (term457 A B C t f op s g h).
Proof. exact (MK_COMB (@lem5989531 C op) (@lem5989528 A B C t f op s g h)). Qed.
Lemma lem5989535 {A B C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term458 A B C f op s g h) = (term459 A B C f op s g h).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5989532 A B C t f op s g h)). Qed.
Lemma lem5989536 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5989537 {A B C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term460 A B C f op s g h) = (term461 A B C f op s g h).
Proof. exact (MK_COMB (@lem5989536 B) (@lem5989535 A B C f op s g h)). Qed.
Lemma lem5989542 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term462 A B C op s g h) = (term463 A B C op s g h).
Proof. exact (fun_ext (fun f : A -> C => @lem5989537 A B C f op s g h)). Qed.
Lemma lem5989543 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem5989544 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term464 A B C op s g h) = (term465 A B C op s g h).
Proof. exact (MK_COMB (@lem5989543 A C) (@lem5989542 A B C op s g h)). Qed.
Lemma lem5989549 {A B C : Type'} (s : A -> Prop) (g : B -> C) (h : A -> B) : (term466 A B C s g h) = (term467 A B C s g h).
Proof. exact (fun_ext (fun op : type1400 C => @lem5989544 A B C op s g h)). Qed.
Lemma lem5989550 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem5989551 {A B C : Type'} (s : A -> Prop) (g : B -> C) (h : A -> B) : (term468 A B C s g h) = (term469 A B C s g h).
Proof. exact (MK_COMB (@lem5989550 C) (@lem5989549 A B C s g h)). Qed.
Lemma lem5989556 {A B C : Type'} (g : B -> C) (h : A -> B) : (term470 A B C g h) = (term471 A B C g h).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5989551 A B C s g h)). Qed.
Lemma lem5989557 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5989558 {A B C : Type'} (g : B -> C) (h : A -> B) : (term472 A B C g h) = (term473 A B C g h).
Proof. exact (MK_COMB (@lem5989557 A) (@lem5989556 A B C g h)). Qed.
Lemma lem5989563 {A B C : Type'} (h : A -> B) : (term474 A B C h) = (term475 A B C h).
Proof. exact (fun_ext (fun g : B -> C => @lem5989558 A B C g h)). Qed.
Lemma lem5989564 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem5989565 {A B C : Type'} (h : A -> B) : (term476 A B C h) = (term477 A B C h).
Proof. exact (MK_COMB (@lem5989564 B C) (@lem5989563 A B C h)). Qed.
Lemma lem5989570 {A B C : Type'} : (term478 A B C) = (term479 A B C).
Proof. exact (fun_ext (fun h : A -> B => @lem5989565 A B C h)). Qed.
Lemma lem5989571 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5989580 {A B C : Type'} : (term480 A B C) = (term481 A B C).
Proof. exact (MK_COMB (@lem5989571 A B) (@lem5989570 A B C)). Qed.
Lemma lem5989581 {A C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : ((@iterate C A op s f) = (@iterate C A op s g)) = ((@iterate C A op s f) = (@iterate C A op s g)).
Proof. exact (eq_refl ((@iterate C A op s f) = (@iterate C A op s g))). Qed.
Lemma lem5989586 {A C : Type'} (s : A -> Prop) (f : A -> C) (g : A -> C) (x : A) : (term482 A C s f g x) = (term482 A C s f g x).
Proof. exact (eq_refl (term482 A C s f g x)). Qed.
Lemma lem5989587 {A C : Type'} (s : A -> Prop) (f : A -> C) (g : A -> C) : (term483 A C s f g) = (term483 A C s f g).
Proof. exact (fun_ext (fun x : A => @lem5989586 A C s f g x)). Qed.
Lemma lem5989588 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5989589 {A C : Type'} (s : A -> Prop) (f : A -> C) (g : A -> C) : (term484 A C s f g) = (term484 A C s f g).
Proof. exact (MK_COMB (@lem5989588 A) (@lem5989587 A C s f g)). Qed.
Lemma lem5989590 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5989591 {A C : Type'} (s : A -> Prop) (f : A -> C) (g : A -> C) : (term485 A C s f g) = (term485 A C s f g).
Proof. exact (MK_COMB (@lem5989590) (@lem5989589 A C s f g)). Qed.
Lemma lem5989592 {A C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term486 A C f op s g) = (term486 A C f op s g).
Proof. exact (MK_COMB (@lem5989591 A C s f g) (@lem5989581 A C f op s g)). Qed.
Lemma lem5989593 {A C : Type'} (f : A -> C) (op : type1400 C) (g : A -> C) : (term487 A C f op g) = (term487 A C f op g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5989592 A C f op s g)). Qed.
Lemma lem5989594 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5989595 {A C : Type'} (f : A -> C) (op : type1400 C) (g : A -> C) : (term488 A C f op g) = (term488 A C f op g).
Proof. exact (MK_COMB (@lem5989594 A) (@lem5989593 A C f op g)). Qed.
Lemma lem5989596 {A C : Type'} (f : A -> C) (op : type1400 C) : (term489 A C f op) = (term489 A C f op).
Proof. exact (fun_ext (fun g : A -> C => @lem5989595 A C f op g)). Qed.
Lemma lem5989597 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem5989598 {A C : Type'} (f : A -> C) (op : type1400 C) : (term490 A C f op) = (term490 A C f op).
Proof. exact (MK_COMB (@lem5989597 A C) (@lem5989596 A C f op)). Qed.
Lemma lem5989599 {A C : Type'} (op : type1400 C) : (term491 A C op) = (term491 A C op).
Proof. exact (fun_ext (fun f : A -> C => @lem5989598 A C f op)). Qed.
Lemma lem5989600 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem5989601 {A C : Type'} (op : type1400 C) : (term492 A C op) = (term492 A C op).
Proof. exact (MK_COMB (@lem5989600 A C) (@lem5989599 A C op)). Qed.
Lemma lem5989604 {C : Type'} (op : type1400 C) : (term66 C op) = (term66 C op).
Proof. exact (eq_refl (term66 C op)). Qed.
Lemma lem5989605 {A C : Type'} (op : type1400 C) : (term493 A C op) = (term493 A C op).
Proof. exact (MK_COMB (@lem5989604 C op) (@lem5989601 A C op)). Qed.
Lemma lem5989606 {A C : Type'} : (term494 A C) = (term494 A C).
Proof. exact (fun_ext (fun op : type1400 C => @lem5989605 A C op)). Qed.
Lemma lem5989607 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem5989608 {A C : Type'} : (term428 A C) = (term428 A C).
Proof. exact (MK_COMB (@lem5989607 C) (@lem5989606 A C)). Qed.
Lemma lem5989609 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5989610 {A C : Type'} : (term437 A C) = (term437 A C).
Proof. exact (MK_COMB (@lem5989609) (@lem5989608 A C)). Qed.
Lemma lem5989611 {B : Type'} (f : B -> B) (op : type1400 B) (s : B -> Prop) (g : B -> B) : ((@iterate B B op s f) = (@iterate B B op s g)) = ((@iterate B B op s f) = (@iterate B B op s g)).
Proof. exact (eq_refl ((@iterate B B op s f) = (@iterate B B op s g))). Qed.
Lemma lem5989616 {B : Type'} (s : B -> Prop) (f : B -> B) (g : B -> B) (x : B) : (term495 B s f g x) = (term495 B s f g x).
Proof. exact (eq_refl (term495 B s f g x)). Qed.
Lemma lem5989617 {B : Type'} (s : B -> Prop) (f : B -> B) (g : B -> B) : (term496 B s f g) = (term496 B s f g).
Proof. exact (fun_ext (fun x : B => @lem5989616 B s f g x)). Qed.
Lemma lem5989618 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5989619 {B : Type'} (s : B -> Prop) (f : B -> B) (g : B -> B) : (term497 B s f g) = (term497 B s f g).
Proof. exact (MK_COMB (@lem5989618 B) (@lem5989617 B s f g)). Qed.
Lemma lem5989620 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5989621 {B : Type'} (s : B -> Prop) (f : B -> B) (g : B -> B) : (term498 B s f g) = (term498 B s f g).
Proof. exact (MK_COMB (@lem5989620) (@lem5989619 B s f g)). Qed.
Lemma lem5989622 {B : Type'} (f : B -> B) (op : type1400 B) (s : B -> Prop) (g : B -> B) : (term499 B f op s g) = (term499 B f op s g).
Proof. exact (MK_COMB (@lem5989621 B s f g) (@lem5989611 B f op s g)). Qed.
Lemma lem5989623 {B : Type'} (f : B -> B) (op : type1400 B) (g : B -> B) : (term500 B f op g) = (term500 B f op g).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5989622 B f op s g)). Qed.
Lemma lem5989624 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5989625 {B : Type'} (f : B -> B) (op : type1400 B) (g : B -> B) : (term501 B f op g) = (term501 B f op g).
Proof. exact (MK_COMB (@lem5989624 B) (@lem5989623 B f op g)). Qed.
Lemma lem5989626 {B : Type'} (f : B -> B) (op : type1400 B) : (term502 B f op) = (term502 B f op).
Proof. exact (fun_ext (fun g : B -> B => @lem5989625 B f op g)). Qed.
Lemma lem5989627 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem5989628 {B : Type'} (f : B -> B) (op : type1400 B) : (term503 B f op) = (term503 B f op).
Proof. exact (MK_COMB (@lem5989627 B) (@lem5989626 B f op)). Qed.
Lemma lem5989629 {B : Type'} (op : type1400 B) : (term504 B op) = (term504 B op).
Proof. exact (fun_ext (fun f : B -> B => @lem5989628 B f op)). Qed.
Lemma lem5989630 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem5989631 {B : Type'} (op : type1400 B) : (term505 B op) = (term505 B op).
Proof. exact (MK_COMB (@lem5989630 B) (@lem5989629 B op)). Qed.
Lemma lem5989634 {B : Type'} (op : type1400 B) : (term66 B op) = (term66 B op).
Proof. exact (eq_refl (term66 B op)). Qed.
Lemma lem5989635 {B : Type'} (op : type1400 B) : (term506 B op) = (term506 B op).
Proof. exact (MK_COMB (@lem5989634 B op) (@lem5989631 B op)). Qed.
Lemma lem5989636 {B : Type'} : (term507 B) = (term507 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5989635 B op)). Qed.
Lemma lem5989637 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5989638 {B : Type'} : (term429 B) = (term429 B).
Proof. exact (MK_COMB (@lem5989637 B) (@lem5989636 B)). Qed.
Lemma lem5989639 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5989640 {B : Type'} : (term438 B) = (term438 B).
Proof. exact (MK_COMB (@lem5989639) (@lem5989638 B)). Qed.
Lemma lem5989641 {A B C : Type'} : (term440 A B C) = (term440 A B C).
Proof. exact (MK_COMB (@lem5989640 B) (@lem5989610 A C)). Qed.
Lemma lem5989642 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : ((@iterate B A op s f) = (@iterate B A op s g)) = ((@iterate B A op s f) = (@iterate B A op s g)).
Proof. exact (eq_refl ((@iterate B A op s f) = (@iterate B A op s g))). Qed.
Lemma lem5989647 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term482 A B s f g x) = (term482 A B s f g x).
Proof. exact (eq_refl (term482 A B s f g x)). Qed.
Lemma lem5989648 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term483 A B s f g) = (term483 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem5989647 A B s f g x)). Qed.
Lemma lem5989649 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5989650 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term484 A B s f g) = (term484 A B s f g).
Proof. exact (MK_COMB (@lem5989649 A) (@lem5989648 A B s f g)). Qed.
Lemma lem5989651 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5989652 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term485 A B s f g) = (term485 A B s f g).
Proof. exact (MK_COMB (@lem5989651) (@lem5989650 A B s f g)). Qed.
Lemma lem5989653 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term486 A B f op s g) = (term486 A B f op s g).
Proof. exact (MK_COMB (@lem5989652 A B s f g) (@lem5989642 A B f op s g)). Qed.
Lemma lem5989654 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term487 A B f op g) = (term487 A B f op g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5989653 A B f op s g)). Qed.
Lemma lem5989655 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5989656 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term488 A B f op g) = (term488 A B f op g).
Proof. exact (MK_COMB (@lem5989655 A) (@lem5989654 A B f op g)). Qed.
Lemma lem5989657 {A B : Type'} (f : A -> B) (op : type1400 B) : (term489 A B f op) = (term489 A B f op).
Proof. exact (fun_ext (fun g : A -> B => @lem5989656 A B f op g)). Qed.
Lemma lem5989658 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5989659 {A B : Type'} (f : A -> B) (op : type1400 B) : (term490 A B f op) = (term490 A B f op).
Proof. exact (MK_COMB (@lem5989658 A B) (@lem5989657 A B f op)). Qed.
Lemma lem5989660 {A B : Type'} (op : type1400 B) : (term491 A B op) = (term491 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5989659 A B f op)). Qed.
Lemma lem5989661 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5989662 {A B : Type'} (op : type1400 B) : (term492 A B op) = (term492 A B op).
Proof. exact (MK_COMB (@lem5989661 A B) (@lem5989660 A B op)). Qed.
Lemma lem5989665 {B : Type'} (op : type1400 B) : (term66 B op) = (term66 B op).
Proof. exact (eq_refl (term66 B op)). Qed.
Lemma lem5989666 {A B : Type'} (op : type1400 B) : (term493 A B op) = (term493 A B op).
Proof. exact (MK_COMB (@lem5989665 B op) (@lem5989662 A B op)). Qed.
Lemma lem5989667 {A B : Type'} : (term494 A B) = (term494 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5989666 A B op)). Qed.
Lemma lem5989668 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5989669 {A B : Type'} : (term428 A B) = (term428 A B).
Proof. exact (MK_COMB (@lem5989668 B) (@lem5989667 A B)). Qed.
Lemma lem5989670 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5989671 {A B : Type'} : (term441 A B) = (term441 A B).
Proof. exact (MK_COMB (@lem5989670) (@lem5989669 A B)). Qed.
Lemma lem5989672 {A B C : Type'} : (term443 A B C) = (term443 A B C).
Proof. exact (MK_COMB (@lem5989671 A B) (@lem5989641 A B C)). Qed.
Lemma lem5989673 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : ((@o A B C f g x) = (term341 A B C f g x)) = ((@o A B C f g x) = (term341 A B C f g x)).
Proof. exact (eq_refl ((@o A B C f g x) = (term341 A B C f g x))). Qed.
Lemma lem5989674 {A B C : Type'} (f : B -> C) (g : A -> B) : (term508 A B C f g) = (term508 A B C f g).
Proof. exact (fun_ext (fun x : A => @lem5989673 A B C f g x)). Qed.
Lemma lem5989675 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5989676 {A B C : Type'} (f : B -> C) (g : A -> B) : (term509 A B C f g) = (term509 A B C f g).
Proof. exact (MK_COMB (@lem5989675 A) (@lem5989674 A B C f g)). Qed.
Lemma lem5989677 {A B C : Type'} (f : B -> C) : (term510 A B C f) = (term510 A B C f).
Proof. exact (fun_ext (fun g : A -> B => @lem5989676 A B C f g)). Qed.
Lemma lem5989678 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5989679 {A B C : Type'} (f : B -> C) : (term511 A B C f) = (term511 A B C f).
Proof. exact (MK_COMB (@lem5989678 A B) (@lem5989677 A B C f)). Qed.
Lemma lem5989680 {A B C : Type'} : (term512 A B C) = (term512 A B C).
Proof. exact (fun_ext (fun f : B -> C => @lem5989679 A B C f)). Qed.
Lemma lem5989681 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem5989682 {A B C : Type'} : (term431 A B C) = (term431 A B C).
Proof. exact (MK_COMB (@lem5989681 B C) (@lem5989680 A B C)). Qed.
Lemma lem5989683 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5989684 {A B C : Type'} : (term444 A B C) = (term444 A B C).
Proof. exact (MK_COMB (@lem5989683) (@lem5989682 A B C)). Qed.
Lemma lem5989685 {A B C : Type'} : (term446 A B C) = (term446 A B C).
Proof. exact (MK_COMB (@lem5989684 A B C) (@lem5989672 A B C)). Qed.
Lemma lem5989686 {A B : Type'} (f : B -> B) (g : A -> B) (x : A) : ((@o A B B f g x) = (term513 A B f g x)) = ((@o A B B f g x) = (term513 A B f g x)).
Proof. exact (eq_refl ((@o A B B f g x) = (term513 A B f g x))). Qed.
Lemma lem5989687 {A B : Type'} (f : B -> B) (g : A -> B) : (term514 A B f g) = (term514 A B f g).
Proof. exact (fun_ext (fun x : A => @lem5989686 A B f g x)). Qed.
Lemma lem5989688 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5989689 {A B : Type'} (f : B -> B) (g : A -> B) : (term515 A B f g) = (term515 A B f g).
Proof. exact (MK_COMB (@lem5989688 A) (@lem5989687 A B f g)). Qed.
Lemma lem5989690 {A B : Type'} (f : B -> B) : (term516 A B f) = (term516 A B f).
Proof. exact (fun_ext (fun g : A -> B => @lem5989689 A B f g)). Qed.
Lemma lem5989691 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5989692 {A B : Type'} (f : B -> B) : (term517 A B f) = (term517 A B f).
Proof. exact (MK_COMB (@lem5989691 A B) (@lem5989690 A B f)). Qed.
Lemma lem5989693 {A B : Type'} : (term518 A B) = (term518 A B).
Proof. exact (fun_ext (fun f : B -> B => @lem5989692 A B f)). Qed.
Lemma lem5989694 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem5989695 {A B : Type'} : (term430 A B) = (term430 A B).
Proof. exact (MK_COMB (@lem5989694 B) (@lem5989693 A B)). Qed.
Lemma lem5989696 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5989697 {A B : Type'} : (term447 A B) = (term447 A B).
Proof. exact (MK_COMB (@lem5989696) (@lem5989695 A B)). Qed.
Lemma lem5989698 {A B C : Type'} : (term449 A B C) = (term449 A B C).
Proof. exact (MK_COMB (@lem5989697 A B) (@lem5989685 A B C)). Qed.
Lemma lem5989703 {A B C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term450 A B C f op s g h) = (term450 A B C f op s g h).
Proof. exact (eq_refl (term450 A B C f op s g h)). Qed.
Lemma lem5989704 {A B C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term452 A B C f op s g h) = (term452 A B C f op s g h).
Proof. exact (MK_COMB (@lem5989703 A B C f op s g h) (@lem5989698 A B C)). Qed.
Lemma lem5989713 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term94 A B C s t g h f x) = (term94 A B C s t g h f x).
Proof. exact (eq_refl (term94 A B C s t g h f x)). Qed.
Lemma lem5989714 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term95 A B C s t g h f) = (term95 A B C s t g h f).
Proof. exact (fun_ext (fun x : A => @lem5989713 A B C s t g h f x)). Qed.
Lemma lem5989715 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5989716 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term38 A B C s t g h f) = (term38 A B C s t g h f).
Proof. exact (MK_COMB (@lem5989715 A) (@lem5989714 A B C s t g h f)). Qed.
Lemma lem5989717 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5989718 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term60 A B C s t g h f) = (term60 A B C s t g h f).
Proof. exact (MK_COMB (@lem5989717) (@lem5989716 A B C s t g h f)). Qed.
Lemma lem5989719 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term454 A B C t f op s g h) = (term454 A B C t f op s g h).
Proof. exact (MK_COMB (@lem5989718 A B C s t g h f) (@lem5989704 A B C f op s g h)). Qed.
Lemma lem5989724 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term96 A B s h x y) = (term96 A B s h x y).
Proof. exact (eq_refl (term96 A B s h x y)). Qed.
Lemma lem5989725 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term97 A B s h y) = (term97 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5989724 A B s h x y)). Qed.
Lemma lem5989726 {A : Type'} : (@ex1 A) = (@ex1 A).
Proof. exact (eq_refl (@ex1 A)). Qed.
Lemma lem5989727 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term98 A B s h y) = (term98 A B s h y).
Proof. exact (MK_COMB (@lem5989726 A) (@lem5989725 A B s h y)). Qed.
Lemma lem5989730 {B : Type'} (y : B) (t : B -> Prop) : (term99 B y t) = (term99 B y t).
Proof. exact (eq_refl (term99 B y t)). Qed.
Lemma lem5989731 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term100 A B t s h y) = (term100 A B t s h y).
Proof. exact (MK_COMB (@lem5989730 B y t) (@lem5989727 A B s h y)). Qed.
Lemma lem5989732 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term101 A B t s h) = (term101 A B t s h).
Proof. exact (fun_ext (fun y : B => @lem5989731 A B t s h y)). Qed.
Lemma lem5989733 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5989734 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term39 A B t s h) = (term39 A B t s h).
Proof. exact (MK_COMB (@lem5989733 B) (@lem5989732 A B t s h)). Qed.
Lemma lem5989735 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5989736 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term63 A B t s h) = (term63 A B t s h).
Proof. exact (MK_COMB (@lem5989735) (@lem5989734 A B t s h)). Qed.
Lemma lem5989737 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term456 A B C t f op s g h) = (term456 A B C t f op s g h).
Proof. exact (MK_COMB (@lem5989736 A B t s h) (@lem5989719 A B C t f op s g h)). Qed.
Lemma lem5989740 {C : Type'} (op : type1400 C) : (term66 C op) = (term66 C op).
Proof. exact (eq_refl (term66 C op)). Qed.
Lemma lem5989741 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term457 A B C t f op s g h) = (term457 A B C t f op s g h).
Proof. exact (MK_COMB (@lem5989740 C op) (@lem5989737 A B C t f op s g h)). Qed.
Lemma lem5989742 {A B C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term459 A B C f op s g h) = (term459 A B C f op s g h).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5989741 A B C t f op s g h)). Qed.
Lemma lem5989743 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5989744 {A B C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term461 A B C f op s g h) = (term461 A B C f op s g h).
Proof. exact (MK_COMB (@lem5989743 B) (@lem5989742 A B C f op s g h)). Qed.
Lemma lem5989745 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term463 A B C op s g h) = (term463 A B C op s g h).
Proof. exact (fun_ext (fun f : A -> C => @lem5989744 A B C f op s g h)). Qed.
Lemma lem5989746 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem5989747 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term465 A B C op s g h) = (term465 A B C op s g h).
Proof. exact (MK_COMB (@lem5989746 A C) (@lem5989745 A B C op s g h)). Qed.
Lemma lem5989748 {A B C : Type'} (s : A -> Prop) (g : B -> C) (h : A -> B) : (term467 A B C s g h) = (term467 A B C s g h).
Proof. exact (fun_ext (fun op : type1400 C => @lem5989747 A B C op s g h)). Qed.
Lemma lem5989749 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem5989750 {A B C : Type'} (s : A -> Prop) (g : B -> C) (h : A -> B) : (term469 A B C s g h) = (term469 A B C s g h).
Proof. exact (MK_COMB (@lem5989749 C) (@lem5989748 A B C s g h)). Qed.
Lemma lem5989751 {A B C : Type'} (g : B -> C) (h : A -> B) : (term471 A B C g h) = (term471 A B C g h).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5989750 A B C s g h)). Qed.
Lemma lem5989752 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5989753 {A B C : Type'} (g : B -> C) (h : A -> B) : (term473 A B C g h) = (term473 A B C g h).
Proof. exact (MK_COMB (@lem5989752 A) (@lem5989751 A B C g h)). Qed.
Lemma lem5989754 {A B C : Type'} (h : A -> B) : (term475 A B C h) = (term475 A B C h).
Proof. exact (fun_ext (fun g : B -> C => @lem5989753 A B C g h)). Qed.
Lemma lem5989755 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem5989756 {A B C : Type'} (h : A -> B) : (term477 A B C h) = (term477 A B C h).
Proof. exact (MK_COMB (@lem5989755 B C) (@lem5989754 A B C h)). Qed.
Lemma lem5989757 {A B C : Type'} : (term479 A B C) = (term479 A B C).
Proof. exact (fun_ext (fun h : A -> B => @lem5989756 A B C h)). Qed.
Lemma lem5989758 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5989759 {A B C : Type'} : (term481 A B C) = (term481 A B C).
Proof. exact (MK_COMB (@lem5989758 A B) (@lem5989757 A B C)). Qed.
Lemma lem5989978 {A B C : Type'} : (term480 A B C) = (term481 A B C).
Proof. exact (TRANS (@lem5989580 A B C) (@lem5989759 A B C)). Qed.
Lemma lem5989979 {A B C : Type'} : (term481 A B C) = (term480 A B C).
Proof. exact (SYM (@lem5989978 A B C)). Qed.
Lemma lem5989981 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (h1 : term39 A B t s h) : term39 A B t s h.
Proof. exact (h1). Qed.
Lemma lem5989982 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term38 A B C s t g h f.
Proof. exact (h1). Qed.
Lemma lem5989985 {A B C : Type'} (h1 : term431 A B C) : term431 A B C.
Proof. exact (h1). Qed.
Lemma lem5989986 {A B : Type'} (h1 : term428 A B) : term428 A B.
Proof. exact (h1). Qed.
Lemma lem5989987 {B : Type'} (h1 : term429 B) : term429 B.
Proof. exact (h1). Qed.
Lemma lem5989988 {A C : Type'} (h1 : term428 A C) : term428 A C.
Proof. exact (h1). Qed.
Lemma lem5989994 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (h1). Qed.
Lemma lem5990004 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term104 A B s h x y) = (term105 A B s h x y).
Proof. exact (@lem17045 (@IN A x s) ((h x) = y)). Qed.
Lemma lem5990009 {A : Type'} (x' : A) (x : A) : (x' = x) = (x' = x).
Proof. exact (eq_refl (x' = x)). Qed.
Lemma lem5990010 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term106 A B s h y x) = (term96 A B s h x y).
Proof. exact (eq_refl (term106 A B s h y x)). Qed.
Lemma lem5990011 {A B : Type'} (s : A -> Prop) (h : A -> B) (x' : A) (y : B) : (term106 A B s h y x') = (term96 A B s h x' y).
Proof. exact (eq_refl (term106 A B s h y x')). Qed.
Lemma lem5990012 {A B : Type'} (s : A -> Prop) (h : A -> B) (x' : A) (y : B) : (term104 A B s h x' y) = (term105 A B s h x' y).
Proof. exact (@lem5990004 A B s h x' y). Qed.
Lemma lem5990013 {A : Type'} (P : A -> Prop) : (@ex1 A P) = (term107 A P).
Proof. exact (@lem18897 A P). Qed.
Lemma lem5990014 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term98 A B s h y) = (term108 A B s h y).
Proof. exact (@lem5990013 A (term97 A B s h y)). Qed.
Lemma lem5990015 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5990016 {A B : Type'} (s : A -> Prop) (h : A -> B) (x' : A) (y : B) : (term109 A B s h y x') = (term104 A B s h x' y).
Proof. exact (MK_COMB (@lem5990015) (@lem5990011 A B s h x' y)). Qed.
Lemma lem5990017 {A B : Type'} (s : A -> Prop) (h : A -> B) (x' : A) (y : B) : (term109 A B s h y x') = (term105 A B s h x' y).
Proof. exact (TRANS (@lem5990016 A B s h x' y) (@lem5990012 A B s h x' y)). Qed.
Lemma lem5990018 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5990019 {A B : Type'} (s : A -> Prop) (h : A -> B) (x' : A) (y : B) : (term110 A B s h y x') = (term111 A B s h x' y).
Proof. exact (MK_COMB (@lem5990018) (@lem5990017 A B s h x' y)). Qed.
Lemma lem5990020 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term112 A B s h y x' x) = (term113 A B s h y x' x).
Proof. exact (MK_COMB (@lem5990019 A B s h x' y) (@lem5990009 A x' x)). Qed.
Lemma lem5990021 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5990022 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term109 A B s h y x) = (term104 A B s h x y).
Proof. exact (MK_COMB (@lem5990021) (@lem5990010 A B s h x y)). Qed.
Lemma lem5990023 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term109 A B s h y x) = (term105 A B s h x y).
Proof. exact (TRANS (@lem5990022 A B s h x y) (@lem5990004 A B s h x y)). Qed.
Lemma lem5990024 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5990025 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term110 A B s h y x) = (term111 A B s h x y).
Proof. exact (MK_COMB (@lem5990024) (@lem5990023 A B s h x y)). Qed.
Lemma lem5990026 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term114 A B s h y x' x) = (term115 A B s h y x' x).
Proof. exact (MK_COMB (@lem5990025 A B s h x y) (@lem5990020 A B s h y x' x)). Qed.
Lemma lem5990027 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term116 A B s h y x) = (term117 A B s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5990026 A B s h y x' x)). Qed.
Lemma lem5990028 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5990029 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term118 A B s h y x) = (term119 A B s h y x).
Proof. exact (MK_COMB (@lem5990028 A) (@lem5990027 A B s h y x)). Qed.
Lemma lem5990030 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term120 A B s h y) = (term121 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5990029 A B s h y x)). Qed.
Lemma lem5990031 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5990032 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term122 A B s h y) = (term123 A B s h y).
Proof. exact (MK_COMB (@lem5990031 A) (@lem5990030 A B s h y)). Qed.
Lemma lem5990033 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term106 A B s h y x) = (term96 A B s h x y).
Proof. exact (eq_refl (term106 A B s h y x)). Qed.
Lemma lem5990034 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term124 A B s h y) = (term97 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5990033 A B s h x y)). Qed.
Lemma lem5990035 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5990036 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term125 A B s h y) = (term126 A B s h y).
Proof. exact (MK_COMB (@lem5990035 A) (@lem5990034 A B s h y)). Qed.
Lemma lem5990037 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5990038 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term127 A B s h y) = (term128 A B s h y).
Proof. exact (MK_COMB (@lem5990037) (@lem5990036 A B s h y)). Qed.
Lemma lem5990039 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term108 A B s h y) = (term129 A B s h y).
Proof. exact (MK_COMB (@lem5990038 A B s h y) (@lem5990032 A B s h y)). Qed.
Lemma lem5990040 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term98 A B s h y) = (term129 A B s h y).
Proof. exact (TRANS (@lem5990014 A B s h y) (@lem5990039 A B s h y)). Qed.
Lemma lem5990042 {B : Type'} (y : B) (t : B -> Prop) : (term130 B y t) = (term130 B y t).
Proof. exact (eq_refl (term130 B y t)). Qed.
Lemma lem5990043 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term131 A B t s h y) = (term132 A B t s h y).
Proof. exact (MK_COMB (@lem5990042 B y t) (@lem5990040 A B s h y)). Qed.
Lemma lem5990044 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term100 A B t s h y) = (term131 A B t s h y).
Proof. exact (@lem17265 (@IN B y t) (term98 A B s h y)). Qed.
Lemma lem5990045 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term100 A B t s h y) = (term132 A B t s h y).
Proof. exact (TRANS (@lem5990044 A B t s h y) (@lem5990043 A B t s h y)). Qed.
Lemma lem5990046 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term101 A B t s h) = (term133 A B t s h).
Proof. exact (fun_ext (fun y : B => @lem5990045 A B t s h y)). Qed.
Lemma lem5990047 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5990048 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term39 A B t s h) = (term134 A B t s h).
Proof. exact (MK_COMB (@lem5990047 B) (@lem5990046 A B t s h)). Qed.
Lemma lem5990150 {A : Type'} (P : Prop) (Q : A -> Prop) : (term135 A P Q) = (term136 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem5990151 {A : Type'} (P : Prop) (Q : A -> Prop) : (term135 A P Q) = (term136 A P Q).
Proof. exact (@lem5990150 A P Q). Qed.
Lemma lem5990152 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term137 A B s h y x) = (term138 A B s h y x).
Proof. exact (@lem5990151 A (term105 A B s h x y) (term139 A B s h y x)). Qed.
Lemma lem5990153 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term140 A B s h y x x') = (term113 A B s h y x' x).
Proof. exact (eq_refl (term140 A B s h y x x')). Qed.
Lemma lem5990154 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term111 A B s h x y) = (term111 A B s h x y).
Proof. exact (eq_refl (term111 A B s h x y)). Qed.
Lemma lem5990155 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term141 A B s h y x x') = (term115 A B s h y x' x).
Proof. exact (MK_COMB (@lem5990154 A B s h x y) (@lem5990153 A B s h y x' x)). Qed.
Lemma lem5990156 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term142 A B s h y x) = (term117 A B s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5990155 A B s h y x' x)). Qed.
Lemma lem5990157 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5990158 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term137 A B s h y x) = (term119 A B s h y x).
Proof. exact (MK_COMB (@lem5990157 A) (@lem5990156 A B s h y x)). Qed.
Lemma lem5990159 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5990160 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term143 A B s h y x) = (term144 A B s h y x).
Proof. exact (MK_COMB (@lem5990159) (@lem5990158 A B s h y x)). Qed.
Lemma lem5990161 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term140 A B s h y x x') = (term113 A B s h y x' x).
Proof. exact (eq_refl (term140 A B s h y x x')). Qed.
Lemma lem5990162 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term145 A B s h y x) = (term139 A B s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5990161 A B s h y x' x)). Qed.
Lemma lem5990163 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5990164 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term146 A B s h y x) = (term147 A B s h y x).
Proof. exact (MK_COMB (@lem5990163 A) (@lem5990162 A B s h y x)). Qed.
Lemma lem5990165 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term111 A B s h x y) = (term111 A B s h x y).
Proof. exact (eq_refl (term111 A B s h x y)). Qed.
Lemma lem5990166 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term138 A B s h y x) = (term148 A B s h y x).
Proof. exact (MK_COMB (@lem5990165 A B s h x y) (@lem5990164 A B s h y x)). Qed.
Lemma lem5990167 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : ((term137 A B s h y x) = (term138 A B s h y x)) = ((term119 A B s h y x) = (term148 A B s h y x)).
Proof. exact (MK_COMB (@lem5990160 A B s h y x) (@lem5990166 A B s h y x)). Qed.
Lemma lem5990168 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term119 A B s h y x) = (term148 A B s h y x).
Proof. exact (EQ_MP (@lem5990167 A B s h y x) (@lem5990152 A B s h y x)). Qed.
Lemma lem5990217 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term121 A B s h y) = (term149 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5990168 A B s h y x)). Qed.
Lemma lem5990218 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5990219 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term123 A B s h y) = (term150 A B s h y).
Proof. exact (MK_COMB (@lem5990218 A) (@lem5990217 A B s h y)). Qed.
Lemma lem5990268 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term128 A B s h y) = (term128 A B s h y).
Proof. exact (eq_refl (term128 A B s h y)). Qed.
Lemma lem5990269 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term129 A B s h y) = (term151 A B s h y).
Proof. exact (MK_COMB (@lem5990268 A B s h y) (@lem5990219 A B s h y)). Qed.
Lemma lem5990270 {B : Type'} (y : B) (t : B -> Prop) : (term130 B y t) = (term130 B y t).
Proof. exact (eq_refl (term130 B y t)). Qed.
Lemma lem5990271 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term132 A B t s h y) = (term152 A B t s h y).
Proof. exact (MK_COMB (@lem5990270 B y t) (@lem5990269 A B s h y)). Qed.
Lemma lem5990272 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term133 A B t s h) = (term153 A B t s h).
Proof. exact (fun_ext (fun y : B => @lem5990271 A B t s h y)). Qed.
Lemma lem5990273 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5990274 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term134 A B t s h) = (term154 A B t s h).
Proof. exact (MK_COMB (@lem5990273 B) (@lem5990272 A B t s h)). Qed.
Lemma lem5990324 {A : Type'} (P : A -> Prop) (Q : Prop) : (term155 A P Q) = (term156 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5990325 {A : Type'} (P : A -> Prop) (Q : Prop) : (term155 A P Q) = (term156 A P Q).
Proof. exact (@lem5990324 A P Q). Qed.
Lemma lem5990326 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term157 A B s h y) = (term158 A B s h y).
Proof. exact (@lem5990325 A (term97 A B s h y) (term150 A B s h y)). Qed.
Lemma lem5990327 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term106 A B s h y x) = (term96 A B s h x y).
Proof. exact (eq_refl (term106 A B s h y x)). Qed.
Lemma lem5990328 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term124 A B s h y) = (term97 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5990327 A B s h x y)). Qed.
Lemma lem5990329 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5990330 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term125 A B s h y) = (term126 A B s h y).
Proof. exact (MK_COMB (@lem5990329 A) (@lem5990328 A B s h y)). Qed.
Lemma lem5990331 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5990332 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term127 A B s h y) = (term128 A B s h y).
Proof. exact (MK_COMB (@lem5990331) (@lem5990330 A B s h y)). Qed.
Lemma lem5990333 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term150 A B s h y) = (term150 A B s h y).
Proof. exact (eq_refl (term150 A B s h y)). Qed.
Lemma lem5990334 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term157 A B s h y) = (term151 A B s h y).
Proof. exact (MK_COMB (@lem5990332 A B s h y) (@lem5990333 A B s h y)). Qed.
Lemma lem5990335 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5990336 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term159 A B s h y) = (term160 A B s h y).
Proof. exact (MK_COMB (@lem5990335) (@lem5990334 A B s h y)). Qed.
Lemma lem5990337 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term106 A B s h y x) = (term96 A B s h x y).
Proof. exact (eq_refl (term106 A B s h y x)). Qed.
Lemma lem5990338 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5990339 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term161 A B s h y x) = (term162 A B s h x y).
Proof. exact (MK_COMB (@lem5990338) (@lem5990337 A B s h x y)). Qed.
Lemma lem5990340 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term150 A B s h y) = (term150 A B s h y).
Proof. exact (eq_refl (term150 A B s h y)). Qed.
Lemma lem5990341 {A B : Type'} (x : A) (s : A -> Prop) (h : A -> B) (y : B) : (term163 A B x s h y) = (term164 A B x s h y).
Proof. exact (MK_COMB (@lem5990339 A B s h x y) (@lem5990340 A B s h y)). Qed.
Lemma lem5990342 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term165 A B s h y) = (term166 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5990341 A B x s h y)). Qed.
Lemma lem5990343 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5990344 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term158 A B s h y) = (term167 A B s h y).
Proof. exact (MK_COMB (@lem5990343 A) (@lem5990342 A B s h y)). Qed.
Lemma lem5990345 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : ((term157 A B s h y) = (term158 A B s h y)) = ((term151 A B s h y) = (term167 A B s h y)).
Proof. exact (MK_COMB (@lem5990336 A B s h y) (@lem5990344 A B s h y)). Qed.
Lemma lem5990346 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term151 A B s h y) = (term167 A B s h y).
Proof. exact (EQ_MP (@lem5990345 A B s h y) (@lem5990326 A B s h y)). Qed.
Lemma lem5990347 {B : Type'} (y : B) (t : B -> Prop) : (term130 B y t) = (term130 B y t).
Proof. exact (eq_refl (term130 B y t)). Qed.
Lemma lem5990348 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term152 A B t s h y) = (term168 A B t s h y).
Proof. exact (MK_COMB (@lem5990347 B y t) (@lem5990346 A B s h y)). Qed.
Lemma lem5990350 {A : Type'} (P : Prop) (Q : A -> Prop) : (term169 A P Q) = (term170 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5990351 {A : Type'} (P : Prop) (Q : A -> Prop) : (term169 A P Q) = (term170 A P Q).
Proof. exact (@lem5990350 A P Q). Qed.
Lemma lem5990352 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term171 A B t s h y) = (term172 A B t s h y).
Proof. exact (@lem5990351 A (term173 B y t) (term166 A B s h y)). Qed.
Lemma lem5990353 {A B : Type'} (x : A) (s : A -> Prop) (h : A -> B) (y : B) : (term174 A B s h y x) = (term164 A B x s h y).
Proof. exact (eq_refl (term174 A B s h y x)). Qed.
Lemma lem5990354 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term175 A B s h y) = (term166 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5990353 A B x s h y)). Qed.
Lemma lem5990355 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5990356 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term176 A B s h y) = (term167 A B s h y).
Proof. exact (MK_COMB (@lem5990355 A) (@lem5990354 A B s h y)). Qed.
Lemma lem5990357 {B : Type'} (y : B) (t : B -> Prop) : (term130 B y t) = (term130 B y t).
Proof. exact (eq_refl (term130 B y t)). Qed.
Lemma lem5990358 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term171 A B t s h y) = (term168 A B t s h y).
Proof. exact (MK_COMB (@lem5990357 B y t) (@lem5990356 A B s h y)). Qed.
Lemma lem5990359 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5990360 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term177 A B t s h y) = (term178 A B t s h y).
Proof. exact (MK_COMB (@lem5990359) (@lem5990358 A B t s h y)). Qed.
Lemma lem5990361 {A B : Type'} (x : A) (s : A -> Prop) (h : A -> B) (y : B) : (term174 A B s h y x) = (term164 A B x s h y).
Proof. exact (eq_refl (term174 A B s h y x)). Qed.
Lemma lem5990362 {B : Type'} (y : B) (t : B -> Prop) : (term130 B y t) = (term130 B y t).
Proof. exact (eq_refl (term130 B y t)). Qed.
Lemma lem5990363 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (h : A -> B) (y : B) : (term179 A B t s h y x) = (term180 A B t x s h y).
Proof. exact (MK_COMB (@lem5990362 B y t) (@lem5990361 A B x s h y)). Qed.
Lemma lem5990364 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term181 A B t s h y) = (term182 A B t s h y).
Proof. exact (fun_ext (fun x : A => @lem5990363 A B t x s h y)). Qed.
Lemma lem5990365 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5990366 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term172 A B t s h y) = (term183 A B t s h y).
Proof. exact (MK_COMB (@lem5990365 A) (@lem5990364 A B t s h y)). Qed.
Lemma lem5990367 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : ((term171 A B t s h y) = (term172 A B t s h y)) = ((term168 A B t s h y) = (term183 A B t s h y)).
Proof. exact (MK_COMB (@lem5990360 A B t s h y) (@lem5990366 A B t s h y)). Qed.
Lemma lem5990368 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term168 A B t s h y) = (term183 A B t s h y).
Proof. exact (EQ_MP (@lem5990367 A B t s h y) (@lem5990352 A B t s h y)). Qed.
Lemma lem5990369 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term152 A B t s h y) = (term183 A B t s h y).
Proof. exact (TRANS (@lem5990348 A B t s h y) (@lem5990368 A B t s h y)). Qed.
Lemma lem5990370 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term153 A B t s h) = (term184 A B t s h).
Proof. exact (fun_ext (fun y : B => @lem5990369 A B t s h y)). Qed.
Lemma lem5990371 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5990372 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term154 A B t s h) = (term185 A B t s h).
Proof. exact (MK_COMB (@lem5990371 B) (@lem5990370 A B t s h)). Qed.
Lemma lem5990374 {A B : Type'} (P : type1413 A B) : (term186 A B P) = (term187 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5990375 {A B : Type'} (P : type1470 A B) : (term188 A B P) = (term189 A B P).
Proof. exact (@lem5990374 B A P). Qed.
Lemma lem5990376 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term190 A B t s h) = (term191 A B t s h).
Proof. exact (@lem5990375 A B (term192 A B t s h)). Qed.
Lemma lem5990377 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term193 A B t s h y) = (term182 A B t s h y).
Proof. exact (eq_refl (term193 A B t s h y)). Qed.
Lemma lem5990378 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5990379 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term194 A B t s h y x) = (term195 A B t s h y x).
Proof. exact (MK_COMB (@lem5990377 A B t s h y) (@lem5990378 A x)). Qed.
Lemma lem5990380 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (h : A -> B) (y : B) : (term195 A B t s h y x) = (term180 A B t x s h y).
Proof. exact (eq_refl (term195 A B t s h y x)). Qed.
Lemma lem5990381 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (h : A -> B) (y : B) : (term194 A B t s h y x) = (term180 A B t x s h y).
Proof. exact (TRANS (@lem5990379 A B t s h y x) (@lem5990380 A B t x s h y)). Qed.
Lemma lem5990382 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term196 A B t s h y) = (term182 A B t s h y).
Proof. exact (fun_ext (fun x : A => @lem5990381 A B t x s h y)). Qed.
Lemma lem5990383 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5990384 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term197 A B t s h y) = (term183 A B t s h y).
Proof. exact (MK_COMB (@lem5990383 A) (@lem5990382 A B t s h y)). Qed.
Lemma lem5990385 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term198 A B t s h) = (term184 A B t s h).
Proof. exact (fun_ext (fun y : B => @lem5990384 A B t s h y)). Qed.
Lemma lem5990386 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5990387 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term190 A B t s h) = (term185 A B t s h).
Proof. exact (MK_COMB (@lem5990386 B) (@lem5990385 A B t s h)). Qed.
Lemma lem5990388 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5990389 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term199 A B t s h) = (term200 A B t s h).
Proof. exact (MK_COMB (@lem5990388) (@lem5990387 A B t s h)). Qed.
Lemma lem5990390 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term193 A B t s h y) = (term182 A B t s h y).
Proof. exact (eq_refl (term193 A B t s h y)). Qed.
Lemma lem5990391 {A B : Type'} (x : B -> A) (y : B) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem5990392 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (x : B -> A) (y : B) : (term201 A B t s h x y) = (term202 A B t s h x y).
Proof. exact (MK_COMB (@lem5990390 A B t s h y) (@lem5990391 A B x y)). Qed.
Lemma lem5990393 {A B : Type'} (t : B -> Prop) (x : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term202 A B t s h x y) = (term203 A B t x s h y).
Proof. exact (eq_refl (term202 A B t s h x y)). Qed.
Lemma lem5990394 {A B : Type'} (t : B -> Prop) (x : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term201 A B t s h x y) = (term203 A B t x s h y).
Proof. exact (TRANS (@lem5990392 A B t s h x y) (@lem5990393 A B t x s h y)). Qed.
Lemma lem5990395 {A B : Type'} (t : B -> Prop) (x : B -> A) (s : A -> Prop) (h : A -> B) : (term204 A B t s h x) = (term205 A B t x s h).
Proof. exact (fun_ext (fun y : B => @lem5990394 A B t x s h y)). Qed.
Lemma lem5990396 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5990397 {A B : Type'} (t : B -> Prop) (x : B -> A) (s : A -> Prop) (h : A -> B) : (term206 A B t s h x) = (term207 A B t x s h).
Proof. exact (MK_COMB (@lem5990396 B) (@lem5990395 A B t x s h)). Qed.
Lemma lem5990398 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term208 A B t s h) = (term209 A B t s h).
Proof. exact (fun_ext (fun x : B -> A => @lem5990397 A B t x s h)). Qed.
Lemma lem5990399 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5990400 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term191 A B t s h) = (term210 A B t s h).
Proof. exact (MK_COMB (@lem5990399 A B) (@lem5990398 A B t s h)). Qed.
Lemma lem5990401 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : ((term190 A B t s h) = (term191 A B t s h)) = ((term185 A B t s h) = (term210 A B t s h)).
Proof. exact (MK_COMB (@lem5990389 A B t s h) (@lem5990400 A B t s h)). Qed.
Lemma lem5990402 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term185 A B t s h) = (term210 A B t s h).
Proof. exact (EQ_MP (@lem5990401 A B t s h) (@lem5990376 A B t s h)). Qed.
Lemma lem5990403 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term154 A B t s h) = (term210 A B t s h).
Proof. exact (TRANS (@lem5990372 A B t s h) (@lem5990402 A B t s h)). Qed.
Lemma lem5990404 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term134 A B t s h) = (term210 A B t s h).
Proof. exact (TRANS (@lem5990274 A B t s h) (@lem5990403 A B t s h)). Qed.
Lemma lem5990405 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term39 A B t s h) = (term210 A B t s h).
Proof. exact (TRANS (@lem5990048 A B t s h) (@lem5990404 A B t s h)). Qed.
Lemma lem5990406 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (h1 : term39 A B t s h) : term210 A B t s h.
Proof. exact (EQ_MP (@lem5990405 A B t s h) (@lem5989981 A B t s h h1)). Qed.
Lemma lem5990417 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term94 A B C s t g h f x) = (term211 A B C s t g h f x).
Proof. exact (@lem17265 (@IN A x s) (term212 A B C t g h f x)). Qed.
Lemma lem5990418 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term95 A B C s t g h f) = (term213 A B C s t g h f).
Proof. exact (fun_ext (fun x : A => @lem5990417 A B C s t g h f x)). Qed.
Lemma lem5990419 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5990472 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term38 A B C s t g h f) = (term214 A B C s t g h f).
Proof. exact (MK_COMB (@lem5990419 A) (@lem5990418 A B C s t g h f)). Qed.
Lemma lem5990473 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term214 A B C s t g h f.
Proof. exact (EQ_MP (@lem5990472 A B C s t g h f) (@lem5989982 A B C s t g h f h1)). Qed.
Lemma lem5990479 {A B C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term427 A B C f op s g h) : term427 A B C f op s g h.
Proof. exact (h1). Qed.
Lemma lem5990507 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : ((@o A B C f g x) = (term341 A B C f g x)) = ((@o A B C f g x) = (term341 A B C f g x)).
Proof. exact (eq_refl ((@o A B C f g x) = (term341 A B C f g x))). Qed.
Lemma lem5990508 {A B C : Type'} (f : B -> C) (g : A -> B) : (term508 A B C f g) = (term508 A B C f g).
Proof. exact (fun_ext (fun x : A => @lem5990507 A B C f g x)). Qed.
Lemma lem5990509 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5990510 {A B C : Type'} (f : B -> C) (g : A -> B) : (term509 A B C f g) = (term509 A B C f g).
Proof. exact (MK_COMB (@lem5990509 A) (@lem5990508 A B C f g)). Qed.
Lemma lem5990511 {A B C : Type'} (f : B -> C) : (term510 A B C f) = (term510 A B C f).
Proof. exact (fun_ext (fun g : A -> B => @lem5990510 A B C f g)). Qed.
Lemma lem5990512 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5990513 {A B C : Type'} (f : B -> C) : (term511 A B C f) = (term511 A B C f).
Proof. exact (MK_COMB (@lem5990512 A B) (@lem5990511 A B C f)). Qed.
Lemma lem5990514 {A B C : Type'} : (term512 A B C) = (term512 A B C).
Proof. exact (fun_ext (fun f : B -> C => @lem5990513 A B C f)). Qed.
Lemma lem5990515 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem5990532 {A B C : Type'} : (term431 A B C) = (term431 A B C).
Proof. exact (MK_COMB (@lem5990515 B C) (@lem5990514 A B C)). Qed.
Lemma lem5990533 {A B C : Type'} (h1 : term431 A B C) : term431 A B C.
Proof. exact (EQ_MP (@lem5990532 A B C) (@lem5989985 A B C h1)). Qed.
Lemma lem5990541 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term519 A B s f g x) = (term520 A B s f g x).
Proof. exact (@lem17362 (@IN A x s) ((f x) = (g x))). Qed.
Lemma lem5990542 {A : Type'} (P : A -> Prop) : (term521 A P) = (term522 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5990543 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term523 A B s f g) = (term524 A B s f g).
Proof. exact (@lem5990542 A (term483 A B s f g)). Qed.
Lemma lem5990544 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term525 A B s f g x) = (term482 A B s f g x).
Proof. exact (eq_refl (term525 A B s f g x)). Qed.
Lemma lem5990545 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5990546 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term526 A B s f g x) = (term519 A B s f g x).
Proof. exact (MK_COMB (@lem5990545) (@lem5990544 A B s f g x)). Qed.
Lemma lem5990547 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term526 A B s f g x) = (term520 A B s f g x).
Proof. exact (TRANS (@lem5990546 A B s f g x) (@lem5990541 A B s f g x)). Qed.
Lemma lem5990548 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term527 A B s f g) = (term528 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem5990547 A B s f g x)). Qed.
Lemma lem5990549 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5990550 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term524 A B s f g) = (term529 A B s f g).
Proof. exact (MK_COMB (@lem5990549 A) (@lem5990548 A B s f g)). Qed.
Lemma lem5990551 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term523 A B s f g) = (term529 A B s f g).
Proof. exact (TRANS (@lem5990543 A B s f g) (@lem5990550 A B s f g)). Qed.
Lemma lem5990552 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : ((@iterate B A op s f) = (@iterate B A op s g)) = ((@iterate B A op s f) = (@iterate B A op s g)).
Proof. exact (eq_refl ((@iterate B A op s f) = (@iterate B A op s g))). Qed.
Lemma lem5990553 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5990554 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term530 A B s f g) = (term531 A B s f g).
Proof. exact (MK_COMB (@lem5990553) (@lem5990551 A B s f g)). Qed.
Lemma lem5990555 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term532 A B f op s g) = (term533 A B f op s g).
Proof. exact (MK_COMB (@lem5990554 A B s f g) (@lem5990552 A B f op s g)). Qed.
Lemma lem5990556 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term486 A B f op s g) = (term532 A B f op s g).
Proof. exact (@lem17265 (term484 A B s f g) ((@iterate B A op s f) = (@iterate B A op s g))). Qed.
Lemma lem5990557 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term486 A B f op s g) = (term533 A B f op s g).
Proof. exact (TRANS (@lem5990556 A B f op s g) (@lem5990555 A B f op s g)). Qed.
Lemma lem5990558 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term487 A B f op g) = (term534 A B f op g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5990557 A B f op s g)). Qed.
Lemma lem5990559 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5990560 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term488 A B f op g) = (term535 A B f op g).
Proof. exact (MK_COMB (@lem5990559 A) (@lem5990558 A B f op g)). Qed.
Lemma lem5990561 {A B : Type'} (f : A -> B) (op : type1400 B) : (term489 A B f op) = (term536 A B f op).
Proof. exact (fun_ext (fun g : A -> B => @lem5990560 A B f op g)). Qed.
Lemma lem5990562 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5990563 {A B : Type'} (f : A -> B) (op : type1400 B) : (term490 A B f op) = (term537 A B f op).
Proof. exact (MK_COMB (@lem5990562 A B) (@lem5990561 A B f op)). Qed.
Lemma lem5990564 {A B : Type'} (op : type1400 B) : (term491 A B op) = (term538 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5990563 A B f op)). Qed.
Lemma lem5990565 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5990566 {A B : Type'} (op : type1400 B) : (term492 A B op) = (term539 A B op).
Proof. exact (MK_COMB (@lem5990565 A B) (@lem5990564 A B op)). Qed.
Lemma lem5990568 {B : Type'} (op : type1400 B) : (term540 B op) = (term540 B op).
Proof. exact (eq_refl (term540 B op)). Qed.
Lemma lem5990569 {A B : Type'} (op : type1400 B) : (term541 A B op) = (term542 A B op).
Proof. exact (MK_COMB (@lem5990568 B op) (@lem5990566 A B op)). Qed.
Lemma lem5990570 {A B : Type'} (op : type1400 B) : (term493 A B op) = (term541 A B op).
Proof. exact (@lem17265 (@monoidal B op) (term492 A B op)). Qed.
Lemma lem5990571 {A B : Type'} (op : type1400 B) : (term493 A B op) = (term542 A B op).
Proof. exact (TRANS (@lem5990570 A B op) (@lem5990569 A B op)). Qed.
Lemma lem5990572 {A B : Type'} : (term494 A B) = (term543 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5990571 A B op)). Qed.
Lemma lem5990573 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5990574 {A B : Type'} : (term428 A B) = (term544 A B).
Proof. exact (MK_COMB (@lem5990573 B) (@lem5990572 A B)). Qed.
Lemma lem5990729 {A : Type'} (P : A -> Prop) (Q : Prop) : (term545 A P Q) = (term546 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5990730 {A : Type'} (P : A -> Prop) (Q : Prop) : (term545 A P Q) = (term546 A P Q).
Proof. exact (@lem5990729 A P Q). Qed.
Lemma lem5990731 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term547 A B f op s g) = (term548 A B f op s g).
Proof. exact (@lem5990730 A (term528 A B s f g) ((@iterate B A op s f) = (@iterate B A op s g))). Qed.
Lemma lem5990732 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term549 A B s f g x) = (term520 A B s f g x).
Proof. exact (eq_refl (term549 A B s f g x)). Qed.
Lemma lem5990733 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term550 A B s f g) = (term528 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem5990732 A B s f g x)). Qed.
Lemma lem5990734 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5990735 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term551 A B s f g) = (term529 A B s f g).
Proof. exact (MK_COMB (@lem5990734 A) (@lem5990733 A B s f g)). Qed.
Lemma lem5990736 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5990737 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term552 A B s f g) = (term531 A B s f g).
Proof. exact (MK_COMB (@lem5990736) (@lem5990735 A B s f g)). Qed.
Lemma lem5990738 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : ((@iterate B A op s f) = (@iterate B A op s g)) = ((@iterate B A op s f) = (@iterate B A op s g)).
Proof. exact (eq_refl ((@iterate B A op s f) = (@iterate B A op s g))). Qed.
Lemma lem5990739 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term547 A B f op s g) = (term533 A B f op s g).
Proof. exact (MK_COMB (@lem5990737 A B s f g) (@lem5990738 A B f op s g)). Qed.
Lemma lem5990740 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5990741 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term553 A B f op s g) = (term554 A B f op s g).
Proof. exact (MK_COMB (@lem5990740) (@lem5990739 A B f op s g)). Qed.
Lemma lem5990742 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term549 A B s f g x) = (term520 A B s f g x).
Proof. exact (eq_refl (term549 A B s f g x)). Qed.
Lemma lem5990743 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5990744 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term555 A B s f g x) = (term556 A B s f g x).
Proof. exact (MK_COMB (@lem5990743) (@lem5990742 A B s f g x)). Qed.
Lemma lem5990745 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : ((@iterate B A op s f) = (@iterate B A op s g)) = ((@iterate B A op s f) = (@iterate B A op s g)).
Proof. exact (eq_refl ((@iterate B A op s f) = (@iterate B A op s g))). Qed.
Lemma lem5990746 {A B : Type'} (x : A) (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term557 A B x f op s g) = (term558 A B x f op s g).
Proof. exact (MK_COMB (@lem5990744 A B s f g x) (@lem5990745 A B f op s g)). Qed.
Lemma lem5990747 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term559 A B f op s g) = (term560 A B f op s g).
Proof. exact (fun_ext (fun x : A => @lem5990746 A B x f op s g)). Qed.
Lemma lem5990748 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5990749 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term548 A B f op s g) = (term561 A B f op s g).
Proof. exact (MK_COMB (@lem5990748 A) (@lem5990747 A B f op s g)). Qed.
Lemma lem5990750 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : ((term547 A B f op s g) = (term548 A B f op s g)) = ((term533 A B f op s g) = (term561 A B f op s g)).
Proof. exact (MK_COMB (@lem5990741 A B f op s g) (@lem5990749 A B f op s g)). Qed.
Lemma lem5990751 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term533 A B f op s g) = (term561 A B f op s g).
Proof. exact (EQ_MP (@lem5990750 A B f op s g) (@lem5990731 A B f op s g)). Qed.
Lemma lem5990752 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term534 A B f op g) = (term562 A B f op g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5990751 A B f op s g)). Qed.
Lemma lem5990753 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5990754 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term535 A B f op g) = (term563 A B f op g).
Proof. exact (MK_COMB (@lem5990753 A) (@lem5990752 A B f op g)). Qed.
Lemma lem5990756 {A B : Type'} (P : type1413 A B) : (term186 A B P) = (term187 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5990757 {A : Type'} (P : type672 A) : (term564 A P) = (term565 A P).
Proof. exact (@lem5990756 (A -> Prop) A P). Qed.
Lemma lem5990758 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term566 A B f op g) = (term567 A B f op g).
Proof. exact (@lem5990757 A (term568 A B f op g)). Qed.
Lemma lem5990759 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term569 A B f op g s) = (term560 A B f op s g).
Proof. exact (eq_refl (term569 A B f op g s)). Qed.
Lemma lem5990760 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5990761 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) (x : A) : (term570 A B f op g s x) = (term571 A B f op s g x).
Proof. exact (MK_COMB (@lem5990759 A B f op s g) (@lem5990760 A x)). Qed.
Lemma lem5990762 {A B : Type'} (x : A) (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term571 A B f op s g x) = (term558 A B x f op s g).
Proof. exact (eq_refl (term571 A B f op s g x)). Qed.
Lemma lem5990763 {A B : Type'} (x : A) (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term570 A B f op g s x) = (term558 A B x f op s g).
Proof. exact (TRANS (@lem5990761 A B f op s g x) (@lem5990762 A B x f op s g)). Qed.
Lemma lem5990764 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term572 A B f op g s) = (term560 A B f op s g).
Proof. exact (fun_ext (fun x : A => @lem5990763 A B x f op s g)). Qed.
Lemma lem5990765 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5990766 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term573 A B f op g s) = (term561 A B f op s g).
Proof. exact (MK_COMB (@lem5990765 A) (@lem5990764 A B f op s g)). Qed.
Lemma lem5990767 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term574 A B f op g) = (term562 A B f op g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5990766 A B f op s g)). Qed.
Lemma lem5990768 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5990769 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term566 A B f op g) = (term563 A B f op g).
Proof. exact (MK_COMB (@lem5990768 A) (@lem5990767 A B f op g)). Qed.
Lemma lem5990770 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5990771 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term575 A B f op g) = (term576 A B f op g).
Proof. exact (MK_COMB (@lem5990770) (@lem5990769 A B f op g)). Qed.
Lemma lem5990772 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term569 A B f op g s) = (term560 A B f op s g).
Proof. exact (eq_refl (term569 A B f op g s)). Qed.
Lemma lem5990773 {A : Type'} (x : type684 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5990774 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : type684 A) (s : A -> Prop) : (term577 A B f op g x s) = (term578 A B f op g x s).
Proof. exact (MK_COMB (@lem5990772 A B f op s g) (@lem5990773 A x s)). Qed.
Lemma lem5990775 {A B : Type'} (x : type684 A) (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term578 A B f op g x s) = (term579 A B x f op s g).
Proof. exact (eq_refl (term578 A B f op g x s)). Qed.
Lemma lem5990776 {A B : Type'} (x : type684 A) (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term577 A B f op g x s) = (term579 A B x f op s g).
Proof. exact (TRANS (@lem5990774 A B f op g x s) (@lem5990775 A B x f op s g)). Qed.
Lemma lem5990777 {A B : Type'} (x : type684 A) (f : A -> B) (op : type1400 B) (g : A -> B) : (term580 A B f op g x) = (term581 A B x f op g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5990776 A B x f op s g)). Qed.
Lemma lem5990778 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5990779 {A B : Type'} (x : type684 A) (f : A -> B) (op : type1400 B) (g : A -> B) : (term582 A B f op g x) = (term583 A B x f op g).
Proof. exact (MK_COMB (@lem5990778 A) (@lem5990777 A B x f op g)). Qed.
Lemma lem5990780 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term584 A B f op g) = (term585 A B f op g).
Proof. exact (fun_ext (fun x : type684 A => @lem5990779 A B x f op g)). Qed.
Lemma lem5990781 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem5990782 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term567 A B f op g) = (term586 A B f op g).
Proof. exact (MK_COMB (@lem5990781 A) (@lem5990780 A B f op g)). Qed.
Lemma lem5990783 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : ((term566 A B f op g) = (term567 A B f op g)) = ((term563 A B f op g) = (term586 A B f op g)).
Proof. exact (MK_COMB (@lem5990771 A B f op g) (@lem5990782 A B f op g)). Qed.
Lemma lem5990784 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term563 A B f op g) = (term586 A B f op g).
Proof. exact (EQ_MP (@lem5990783 A B f op g) (@lem5990758 A B f op g)). Qed.
Lemma lem5990785 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term535 A B f op g) = (term586 A B f op g).
Proof. exact (TRANS (@lem5990754 A B f op g) (@lem5990784 A B f op g)). Qed.
Lemma lem5990786 {A B : Type'} (f : A -> B) (op : type1400 B) : (term536 A B f op) = (term587 A B f op).
Proof. exact (fun_ext (fun g : A -> B => @lem5990785 A B f op g)). Qed.
Lemma lem5990787 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5990788 {A B : Type'} (f : A -> B) (op : type1400 B) : (term537 A B f op) = (term588 A B f op).
Proof. exact (MK_COMB (@lem5990787 A B) (@lem5990786 A B f op)). Qed.
Lemma lem5990790 {A B : Type'} (P : type1413 A B) : (term186 A B P) = (term187 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5990791 {A B : Type'} (P : type503 A B) : (term589 A B P) = (term590 A B P).
Proof. exact (@lem5990790 (A -> B) (type684 A) P). Qed.
Lemma lem5990792 {A B : Type'} (f : A -> B) (op : type1400 B) : (term591 A B f op) = (term592 A B f op).
Proof. exact (@lem5990791 A B (term593 A B f op)). Qed.
Lemma lem5990793 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term594 A B f op g) = (term585 A B f op g).
Proof. exact (eq_refl (term594 A B f op g)). Qed.
Lemma lem5990794 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5990795 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : type684 A) : (term595 A B f op g x) = (term596 A B f op g x).
Proof. exact (MK_COMB (@lem5990793 A B f op g) (@lem5990794 A x)). Qed.
Lemma lem5990796 {A B : Type'} (x : type684 A) (f : A -> B) (op : type1400 B) (g : A -> B) : (term596 A B f op g x) = (term583 A B x f op g).
Proof. exact (eq_refl (term596 A B f op g x)). Qed.
Lemma lem5990797 {A B : Type'} (x : type684 A) (f : A -> B) (op : type1400 B) (g : A -> B) : (term595 A B f op g x) = (term583 A B x f op g).
Proof. exact (TRANS (@lem5990795 A B f op g x) (@lem5990796 A B x f op g)). Qed.
Lemma lem5990798 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term597 A B f op g) = (term585 A B f op g).
Proof. exact (fun_ext (fun x : type684 A => @lem5990797 A B x f op g)). Qed.
Lemma lem5990799 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem5990800 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term598 A B f op g) = (term586 A B f op g).
Proof. exact (MK_COMB (@lem5990799 A) (@lem5990798 A B f op g)). Qed.
Lemma lem5990801 {A B : Type'} (f : A -> B) (op : type1400 B) : (term599 A B f op) = (term587 A B f op).
Proof. exact (fun_ext (fun g : A -> B => @lem5990800 A B f op g)). Qed.
Lemma lem5990802 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5990803 {A B : Type'} (f : A -> B) (op : type1400 B) : (term591 A B f op) = (term588 A B f op).
Proof. exact (MK_COMB (@lem5990802 A B) (@lem5990801 A B f op)). Qed.
Lemma lem5990804 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5990805 {A B : Type'} (f : A -> B) (op : type1400 B) : (term600 A B f op) = (term601 A B f op).
Proof. exact (MK_COMB (@lem5990804) (@lem5990803 A B f op)). Qed.
Lemma lem5990806 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term594 A B f op g) = (term585 A B f op g).
Proof. exact (eq_refl (term594 A B f op g)). Qed.
Lemma lem5990807 {A B : Type'} (x : type529 A B) (g : A -> B) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem5990808 {A B : Type'} (f : A -> B) (op : type1400 B) (x : type529 A B) (g : A -> B) : (term602 A B f op x g) = (term603 A B f op x g).
Proof. exact (MK_COMB (@lem5990806 A B f op g) (@lem5990807 A B x g)). Qed.
Lemma lem5990809 {A B : Type'} (x : type529 A B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term603 A B f op x g) = (term604 A B x f op g).
Proof. exact (eq_refl (term603 A B f op x g)). Qed.
Lemma lem5990810 {A B : Type'} (x : type529 A B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term602 A B f op x g) = (term604 A B x f op g).
Proof. exact (TRANS (@lem5990808 A B f op x g) (@lem5990809 A B x f op g)). Qed.
Lemma lem5990811 {A B : Type'} (x : type529 A B) (f : A -> B) (op : type1400 B) : (term605 A B f op x) = (term606 A B x f op).
Proof. exact (fun_ext (fun g : A -> B => @lem5990810 A B x f op g)). Qed.
Lemma lem5990812 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5990813 {A B : Type'} (x : type529 A B) (f : A -> B) (op : type1400 B) : (term607 A B f op x) = (term608 A B x f op).
Proof. exact (MK_COMB (@lem5990812 A B) (@lem5990811 A B x f op)). Qed.
Lemma lem5990814 {A B : Type'} (f : A -> B) (op : type1400 B) : (term609 A B f op) = (term610 A B f op).
Proof. exact (fun_ext (fun x : type529 A B => @lem5990813 A B x f op)). Qed.
Lemma lem5990815 {A B : Type'} : (@ex ((A -> B) -> (A -> Prop) -> A)) = (@ex ((A -> B) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> Prop) -> A))). Qed.
Lemma lem5990816 {A B : Type'} (f : A -> B) (op : type1400 B) : (term592 A B f op) = (term611 A B f op).
Proof. exact (MK_COMB (@lem5990815 A B) (@lem5990814 A B f op)). Qed.
Lemma lem5990817 {A B : Type'} (f : A -> B) (op : type1400 B) : ((term591 A B f op) = (term592 A B f op)) = ((term588 A B f op) = (term611 A B f op)).
Proof. exact (MK_COMB (@lem5990805 A B f op) (@lem5990816 A B f op)). Qed.
Lemma lem5990818 {A B : Type'} (f : A -> B) (op : type1400 B) : (term588 A B f op) = (term611 A B f op).
Proof. exact (EQ_MP (@lem5990817 A B f op) (@lem5990792 A B f op)). Qed.
Lemma lem5990819 {A B : Type'} (f : A -> B) (op : type1400 B) : (term537 A B f op) = (term611 A B f op).
Proof. exact (TRANS (@lem5990788 A B f op) (@lem5990818 A B f op)). Qed.
Lemma lem5990820 {A B : Type'} (op : type1400 B) : (term538 A B op) = (term612 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5990819 A B f op)). Qed.
Lemma lem5990821 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5990822 {A B : Type'} (op : type1400 B) : (term539 A B op) = (term613 A B op).
Proof. exact (MK_COMB (@lem5990821 A B) (@lem5990820 A B op)). Qed.
Lemma lem5990824 {A B : Type'} (P : type1413 A B) : (term186 A B P) = (term187 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5990825 {A B : Type'} (P : type492 A B) : (term614 A B P) = (term615 A B P).
Proof. exact (@lem5990824 (A -> B) (type529 A B) P). Qed.
Lemma lem5990826 {A B : Type'} (op : type1400 B) : (term616 A B op) = (term617 A B op).
Proof. exact (@lem5990825 A B (term618 A B op)). Qed.
Lemma lem5990827 {A B : Type'} (f : A -> B) (op : type1400 B) : (term619 A B op f) = (term610 A B f op).
Proof. exact (eq_refl (term619 A B op f)). Qed.
Lemma lem5990828 {A B : Type'} (x : type529 A B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5990829 {A B : Type'} (f : A -> B) (op : type1400 B) (x : type529 A B) : (term620 A B op f x) = (term621 A B f op x).
Proof. exact (MK_COMB (@lem5990827 A B f op) (@lem5990828 A B x)). Qed.
Lemma lem5990830 {A B : Type'} (x : type529 A B) (f : A -> B) (op : type1400 B) : (term621 A B f op x) = (term608 A B x f op).
Proof. exact (eq_refl (term621 A B f op x)). Qed.
Lemma lem5990831 {A B : Type'} (x : type529 A B) (f : A -> B) (op : type1400 B) : (term620 A B op f x) = (term608 A B x f op).
Proof. exact (TRANS (@lem5990829 A B f op x) (@lem5990830 A B x f op)). Qed.
Lemma lem5990832 {A B : Type'} (f : A -> B) (op : type1400 B) : (term622 A B op f) = (term610 A B f op).
Proof. exact (fun_ext (fun x : type529 A B => @lem5990831 A B x f op)). Qed.
Lemma lem5990833 {A B : Type'} : (@ex ((A -> B) -> (A -> Prop) -> A)) = (@ex ((A -> B) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> Prop) -> A))). Qed.
Lemma lem5990834 {A B : Type'} (f : A -> B) (op : type1400 B) : (term623 A B op f) = (term611 A B f op).
Proof. exact (MK_COMB (@lem5990833 A B) (@lem5990832 A B f op)). Qed.
Lemma lem5990835 {A B : Type'} (op : type1400 B) : (term624 A B op) = (term612 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5990834 A B f op)). Qed.
Lemma lem5990836 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5990837 {A B : Type'} (op : type1400 B) : (term616 A B op) = (term613 A B op).
Proof. exact (MK_COMB (@lem5990836 A B) (@lem5990835 A B op)). Qed.
Lemma lem5990838 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5990839 {A B : Type'} (op : type1400 B) : (term625 A B op) = (term626 A B op).
Proof. exact (MK_COMB (@lem5990838) (@lem5990837 A B op)). Qed.
Lemma lem5990840 {A B : Type'} (f : A -> B) (op : type1400 B) : (term619 A B op f) = (term610 A B f op).
Proof. exact (eq_refl (term619 A B op f)). Qed.
Lemma lem5990841 {A B : Type'} (x : type514 A B) (f : A -> B) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem5990842 {A B : Type'} (op : type1400 B) (x : type514 A B) (f : A -> B) : (term627 A B op x f) = (term628 A B op x f).
Proof. exact (MK_COMB (@lem5990840 A B f op) (@lem5990841 A B x f)). Qed.
Lemma lem5990843 {A B : Type'} (x : type514 A B) (f : A -> B) (op : type1400 B) : (term628 A B op x f) = (term629 A B x f op).
Proof. exact (eq_refl (term628 A B op x f)). Qed.
Lemma lem5990844 {A B : Type'} (x : type514 A B) (f : A -> B) (op : type1400 B) : (term627 A B op x f) = (term629 A B x f op).
Proof. exact (TRANS (@lem5990842 A B op x f) (@lem5990843 A B x f op)). Qed.
Lemma lem5990845 {A B : Type'} (x : type514 A B) (op : type1400 B) : (term630 A B op x) = (term631 A B x op).
Proof. exact (fun_ext (fun f : A -> B => @lem5990844 A B x f op)). Qed.
Lemma lem5990846 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5990847 {A B : Type'} (x : type514 A B) (op : type1400 B) : (term632 A B op x) = (term633 A B x op).
Proof. exact (MK_COMB (@lem5990846 A B) (@lem5990845 A B x op)). Qed.
Lemma lem5990848 {A B : Type'} (op : type1400 B) : (term634 A B op) = (term635 A B op).
Proof. exact (fun_ext (fun x : type514 A B => @lem5990847 A B x op)). Qed.
Lemma lem5990849 {A B : Type'} : (@ex ((A -> B) -> (A -> B) -> (A -> Prop) -> A)) = (@ex ((A -> B) -> (A -> B) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> (A -> Prop) -> A))). Qed.
Lemma lem5990850 {A B : Type'} (op : type1400 B) : (term617 A B op) = (term636 A B op).
Proof. exact (MK_COMB (@lem5990849 A B) (@lem5990848 A B op)). Qed.
Lemma lem5990851 {A B : Type'} (op : type1400 B) : ((term616 A B op) = (term617 A B op)) = ((term613 A B op) = (term636 A B op)).
Proof. exact (MK_COMB (@lem5990839 A B op) (@lem5990850 A B op)). Qed.
Lemma lem5990852 {A B : Type'} (op : type1400 B) : (term613 A B op) = (term636 A B op).
Proof. exact (EQ_MP (@lem5990851 A B op) (@lem5990826 A B op)). Qed.
Lemma lem5990853 {A B : Type'} (op : type1400 B) : (term539 A B op) = (term636 A B op).
Proof. exact (TRANS (@lem5990822 A B op) (@lem5990852 A B op)). Qed.
Lemma lem5990854 {B : Type'} (op : type1400 B) : (term540 B op) = (term540 B op).
Proof. exact (eq_refl (term540 B op)). Qed.
Lemma lem5990855 {A B : Type'} (op : type1400 B) : (term542 A B op) = (term637 A B op).
Proof. exact (MK_COMB (@lem5990854 B op) (@lem5990853 A B op)). Qed.
Lemma lem5990857 {A : Type'} (P : Prop) (Q : A -> Prop) : (term169 A P Q) = (term170 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5990858 {A B : Type'} (P : Prop) (Q : type93 A B) : (term638 A B P Q) = (term639 A B P Q).
Proof. exact (@lem5990857 (type514 A B) P Q). Qed.
Lemma lem5990859 {A B : Type'} (op : type1400 B) : (term640 A B op) = (term641 A B op).
Proof. exact (@lem5990858 A B (term642 B op) (term635 A B op)). Qed.
Lemma lem5990860 {A B : Type'} (x : type514 A B) (op : type1400 B) : (term643 A B op x) = (term633 A B x op).
Proof. exact (eq_refl (term643 A B op x)). Qed.
Lemma lem5990861 {A B : Type'} (op : type1400 B) : (term644 A B op) = (term635 A B op).
Proof. exact (fun_ext (fun x : type514 A B => @lem5990860 A B x op)). Qed.
Lemma lem5990862 {A B : Type'} : (@ex ((A -> B) -> (A -> B) -> (A -> Prop) -> A)) = (@ex ((A -> B) -> (A -> B) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> (A -> Prop) -> A))). Qed.
Lemma lem5990863 {A B : Type'} (op : type1400 B) : (term645 A B op) = (term636 A B op).
Proof. exact (MK_COMB (@lem5990862 A B) (@lem5990861 A B op)). Qed.
Lemma lem5990864 {B : Type'} (op : type1400 B) : (term540 B op) = (term540 B op).
Proof. exact (eq_refl (term540 B op)). Qed.
Lemma lem5990865 {A B : Type'} (op : type1400 B) : (term640 A B op) = (term637 A B op).
Proof. exact (MK_COMB (@lem5990864 B op) (@lem5990863 A B op)). Qed.
Lemma lem5990866 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5990867 {A B : Type'} (op : type1400 B) : (term646 A B op) = (term647 A B op).
Proof. exact (MK_COMB (@lem5990866) (@lem5990865 A B op)). Qed.
Lemma lem5990868 {A B : Type'} (x : type514 A B) (op : type1400 B) : (term643 A B op x) = (term633 A B x op).
Proof. exact (eq_refl (term643 A B op x)). Qed.
Lemma lem5990869 {B : Type'} (op : type1400 B) : (term540 B op) = (term540 B op).
Proof. exact (eq_refl (term540 B op)). Qed.
Lemma lem5990870 {A B : Type'} (x : type514 A B) (op : type1400 B) : (term648 A B op x) = (term649 A B x op).
Proof. exact (MK_COMB (@lem5990869 B op) (@lem5990868 A B x op)). Qed.
Lemma lem5990871 {A B : Type'} (op : type1400 B) : (term650 A B op) = (term651 A B op).
Proof. exact (fun_ext (fun x : type514 A B => @lem5990870 A B x op)). Qed.
Lemma lem5990872 {A B : Type'} : (@ex ((A -> B) -> (A -> B) -> (A -> Prop) -> A)) = (@ex ((A -> B) -> (A -> B) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> (A -> Prop) -> A))). Qed.
Lemma lem5990873 {A B : Type'} (op : type1400 B) : (term641 A B op) = (term652 A B op).
Proof. exact (MK_COMB (@lem5990872 A B) (@lem5990871 A B op)). Qed.
Lemma lem5990874 {A B : Type'} (op : type1400 B) : ((term640 A B op) = (term641 A B op)) = ((term637 A B op) = (term652 A B op)).
Proof. exact (MK_COMB (@lem5990867 A B op) (@lem5990873 A B op)). Qed.
Lemma lem5990875 {A B : Type'} (op : type1400 B) : (term637 A B op) = (term652 A B op).
Proof. exact (EQ_MP (@lem5990874 A B op) (@lem5990859 A B op)). Qed.
Lemma lem5990876 {A B : Type'} (op : type1400 B) : (term542 A B op) = (term652 A B op).
Proof. exact (TRANS (@lem5990855 A B op) (@lem5990875 A B op)). Qed.
Lemma lem5990877 {A B : Type'} : (term543 A B) = (term653 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5990876 A B op)). Qed.
Lemma lem5990878 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5990879 {A B : Type'} : (term544 A B) = (term654 A B).
Proof. exact (MK_COMB (@lem5990878 B) (@lem5990877 A B)). Qed.
Lemma lem5990881 {A B : Type'} (P : type1413 A B) : (term186 A B P) = (term187 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5990882 {A B : Type'} (P : type746 A B) : (term655 A B P) = (term656 A B P).
Proof. exact (@lem5990881 (type1400 B) (type514 A B) P). Qed.
Lemma lem5990883 {A B : Type'} : (term657 A B) = (term658 A B).
Proof. exact (@lem5990882 A B (term659 A B)). Qed.
Lemma lem5990884 {A B : Type'} (op : type1400 B) : (term660 A B op) = (term651 A B op).
Proof. exact (eq_refl (term660 A B op)). Qed.
Lemma lem5990885 {A B : Type'} (x : type514 A B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5990886 {A B : Type'} (op : type1400 B) (x : type514 A B) : (term661 A B op x) = (term662 A B op x).
Proof. exact (MK_COMB (@lem5990884 A B op) (@lem5990885 A B x)). Qed.
Lemma lem5990887 {A B : Type'} (x : type514 A B) (op : type1400 B) : (term662 A B op x) = (term649 A B x op).
Proof. exact (eq_refl (term662 A B op x)). Qed.
Lemma lem5990888 {A B : Type'} (x : type514 A B) (op : type1400 B) : (term661 A B op x) = (term649 A B x op).
Proof. exact (TRANS (@lem5990886 A B op x) (@lem5990887 A B x op)). Qed.
Lemma lem5990889 {A B : Type'} (op : type1400 B) : (term663 A B op) = (term651 A B op).
Proof. exact (fun_ext (fun x : type514 A B => @lem5990888 A B x op)). Qed.
Lemma lem5990890 {A B : Type'} : (@ex ((A -> B) -> (A -> B) -> (A -> Prop) -> A)) = (@ex ((A -> B) -> (A -> B) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> (A -> Prop) -> A))). Qed.
Lemma lem5990891 {A B : Type'} (op : type1400 B) : (term664 A B op) = (term652 A B op).
Proof. exact (MK_COMB (@lem5990890 A B) (@lem5990889 A B op)). Qed.
Lemma lem5990892 {A B : Type'} : (term665 A B) = (term653 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5990891 A B op)). Qed.
Lemma lem5990893 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5990894 {A B : Type'} : (term657 A B) = (term654 A B).
Proof. exact (MK_COMB (@lem5990893 B) (@lem5990892 A B)). Qed.
Lemma lem5990895 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5990896 {A B : Type'} : (term666 A B) = (term667 A B).
Proof. exact (MK_COMB (@lem5990895) (@lem5990894 A B)). Qed.
Lemma lem5990897 {A B : Type'} (op : type1400 B) : (term660 A B op) = (term651 A B op).
Proof. exact (eq_refl (term660 A B op)). Qed.
Lemma lem5990898 {A B : Type'} (x : type747 A B) (op : type1400 B) : (x op) = (x op).
Proof. exact (eq_refl (x op)). Qed.
Lemma lem5990899 {A B : Type'} (x : type747 A B) (op : type1400 B) : (term668 A B x op) = (term669 A B x op).
Proof. exact (MK_COMB (@lem5990897 A B op) (@lem5990898 A B x op)). Qed.
Lemma lem5990900 {A B : Type'} (x : type747 A B) (op : type1400 B) : (term669 A B x op) = (term670 A B x op).
Proof. exact (eq_refl (term669 A B x op)). Qed.
Lemma lem5990901 {A B : Type'} (x : type747 A B) (op : type1400 B) : (term668 A B x op) = (term670 A B x op).
Proof. exact (TRANS (@lem5990899 A B x op) (@lem5990900 A B x op)). Qed.
Lemma lem5990902 {A B : Type'} (x : type747 A B) : (term671 A B x) = (term672 A B x).
Proof. exact (fun_ext (fun op : type1400 B => @lem5990901 A B x op)). Qed.
Lemma lem5990903 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5990904 {A B : Type'} (x : type747 A B) : (term673 A B x) = (term674 A B x).
Proof. exact (MK_COMB (@lem5990903 B) (@lem5990902 A B x)). Qed.
Lemma lem5990905 {A B : Type'} : (term675 A B) = (term676 A B).
Proof. exact (fun_ext (fun x : type747 A B => @lem5990904 A B x)). Qed.
Lemma lem5990906 {A B : Type'} : (@ex ((B -> B -> B) -> (A -> B) -> (A -> B) -> (A -> Prop) -> A)) = (@ex ((B -> B -> B) -> (A -> B) -> (A -> B) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> (A -> B) -> (A -> B) -> (A -> Prop) -> A))). Qed.
Lemma lem5990907 {A B : Type'} : (term658 A B) = (term677 A B).
Proof. exact (MK_COMB (@lem5990906 A B) (@lem5990905 A B)). Qed.
Lemma lem5990908 {A B : Type'} : ((term657 A B) = (term658 A B)) = ((term654 A B) = (term677 A B)).
Proof. exact (MK_COMB (@lem5990896 A B) (@lem5990907 A B)). Qed.
Lemma lem5990909 {A B : Type'} : (term654 A B) = (term677 A B).
Proof. exact (EQ_MP (@lem5990908 A B) (@lem5990883 A B)). Qed.
Lemma lem5990911 {A B : Type'} : (term544 A B) = (term677 A B).
Proof. exact (TRANS (@lem5990879 A B) (@lem5990909 A B)). Qed.
Lemma lem5990912 {A B : Type'} : (term428 A B) = (term677 A B).
Proof. exact (TRANS (@lem5990574 A B) (@lem5990911 A B)). Qed.
Lemma lem5990913 {A B : Type'} (h1 : term428 A B) : term677 A B.
Proof. exact (EQ_MP (@lem5990912 A B) (@lem5989986 A B h1)). Qed.
Lemma lem5990921 {B : Type'} (s : B -> Prop) (f : B -> B) (g : B -> B) (x : B) : (term678 B s f g x) = (term679 B s f g x).
Proof. exact (@lem17362 (@IN B x s) ((f x) = (g x))). Qed.
Lemma lem5990922 {B : Type'} (P : B -> Prop) : (term521 B P) = (term522 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem5990923 {B : Type'} (s : B -> Prop) (f : B -> B) (g : B -> B) : (term680 B s f g) = (term681 B s f g).
Proof. exact (@lem5990922 B (term496 B s f g)). Qed.
Lemma lem5990924 {B : Type'} (s : B -> Prop) (f : B -> B) (g : B -> B) (x : B) : (term682 B s f g x) = (term495 B s f g x).
Proof. exact (eq_refl (term682 B s f g x)). Qed.
Lemma lem5990925 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5990926 {B : Type'} (s : B -> Prop) (f : B -> B) (g : B -> B) (x : B) : (term683 B s f g x) = (term678 B s f g x).
Proof. exact (MK_COMB (@lem5990925) (@lem5990924 B s f g x)). Qed.
Lemma lem5990927 {B : Type'} (s : B -> Prop) (f : B -> B) (g : B -> B) (x : B) : (term683 B s f g x) = (term679 B s f g x).
Proof. exact (TRANS (@lem5990926 B s f g x) (@lem5990921 B s f g x)). Qed.
Lemma lem5990928 {B : Type'} (s : B -> Prop) (f : B -> B) (g : B -> B) : (term684 B s f g) = (term685 B s f g).
Proof. exact (fun_ext (fun x : B => @lem5990927 B s f g x)). Qed.
Lemma lem5990929 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5990930 {B : Type'} (s : B -> Prop) (f : B -> B) (g : B -> B) : (term681 B s f g) = (term686 B s f g).
Proof. exact (MK_COMB (@lem5990929 B) (@lem5990928 B s f g)). Qed.
Lemma lem5990931 {B : Type'} (s : B -> Prop) (f : B -> B) (g : B -> B) : (term680 B s f g) = (term686 B s f g).
Proof. exact (TRANS (@lem5990923 B s f g) (@lem5990930 B s f g)). Qed.
Lemma lem5990932 {B : Type'} (f : B -> B) (op : type1400 B) (s : B -> Prop) (g : B -> B) : ((@iterate B B op s f) = (@iterate B B op s g)) = ((@iterate B B op s f) = (@iterate B B op s g)).
Proof. exact (eq_refl ((@iterate B B op s f) = (@iterate B B op s g))). Qed.
Lemma lem5990933 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5990934 {B : Type'} (s : B -> Prop) (f : B -> B) (g : B -> B) : (term687 B s f g) = (term688 B s f g).
Proof. exact (MK_COMB (@lem5990933) (@lem5990931 B s f g)). Qed.
Lemma lem5990935 {B : Type'} (f : B -> B) (op : type1400 B) (s : B -> Prop) (g : B -> B) : (term689 B f op s g) = (term690 B f op s g).
Proof. exact (MK_COMB (@lem5990934 B s f g) (@lem5990932 B f op s g)). Qed.
Lemma lem5990936 {B : Type'} (f : B -> B) (op : type1400 B) (s : B -> Prop) (g : B -> B) : (term499 B f op s g) = (term689 B f op s g).
Proof. exact (@lem17265 (term497 B s f g) ((@iterate B B op s f) = (@iterate B B op s g))). Qed.
Lemma lem5990937 {B : Type'} (f : B -> B) (op : type1400 B) (s : B -> Prop) (g : B -> B) : (term499 B f op s g) = (term690 B f op s g).
Proof. exact (TRANS (@lem5990936 B f op s g) (@lem5990935 B f op s g)). Qed.
Lemma lem5990938 {B : Type'} (f : B -> B) (op : type1400 B) (g : B -> B) : (term500 B f op g) = (term691 B f op g).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5990937 B f op s g)). Qed.
Lemma lem5990939 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5990940 {B : Type'} (f : B -> B) (op : type1400 B) (g : B -> B) : (term501 B f op g) = (term692 B f op g).
Proof. exact (MK_COMB (@lem5990939 B) (@lem5990938 B f op g)). Qed.
Lemma lem5990941 {B : Type'} (f : B -> B) (op : type1400 B) : (term502 B f op) = (term693 B f op).
Proof. exact (fun_ext (fun g : B -> B => @lem5990940 B f op g)). Qed.
Lemma lem5990942 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem5990943 {B : Type'} (f : B -> B) (op : type1400 B) : (term503 B f op) = (term694 B f op).
Proof. exact (MK_COMB (@lem5990942 B) (@lem5990941 B f op)). Qed.
Lemma lem5990944 {B : Type'} (op : type1400 B) : (term504 B op) = (term695 B op).
Proof. exact (fun_ext (fun f : B -> B => @lem5990943 B f op)). Qed.
Lemma lem5990945 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem5990946 {B : Type'} (op : type1400 B) : (term505 B op) = (term696 B op).
Proof. exact (MK_COMB (@lem5990945 B) (@lem5990944 B op)). Qed.
Lemma lem5990948 {B : Type'} (op : type1400 B) : (term540 B op) = (term540 B op).
Proof. exact (eq_refl (term540 B op)). Qed.
Lemma lem5990949 {B : Type'} (op : type1400 B) : (term697 B op) = (term698 B op).
Proof. exact (MK_COMB (@lem5990948 B op) (@lem5990946 B op)). Qed.
Lemma lem5990950 {B : Type'} (op : type1400 B) : (term506 B op) = (term697 B op).
Proof. exact (@lem17265 (@monoidal B op) (term505 B op)). Qed.
Lemma lem5990951 {B : Type'} (op : type1400 B) : (term506 B op) = (term698 B op).
Proof. exact (TRANS (@lem5990950 B op) (@lem5990949 B op)). Qed.
Lemma lem5990952 {B : Type'} : (term507 B) = (term699 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5990951 B op)). Qed.
Lemma lem5990953 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5990954 {B : Type'} : (term429 B) = (term700 B).
Proof. exact (MK_COMB (@lem5990953 B) (@lem5990952 B)). Qed.
Lemma lem5991109 {A : Type'} (P : A -> Prop) (Q : Prop) : (term545 A P Q) = (term546 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5991110 {B : Type'} (P : B -> Prop) (Q : Prop) : (term545 B P Q) = (term546 B P Q).
Proof. exact (@lem5991109 B P Q). Qed.
Lemma lem5991111 {B : Type'} (f : B -> B) (op : type1400 B) (s : B -> Prop) (g : B -> B) : (term701 B f op s g) = (term702 B f op s g).
Proof. exact (@lem5991110 B (term685 B s f g) ((@iterate B B op s f) = (@iterate B B op s g))). Qed.
Lemma lem5991112 {B : Type'} (s : B -> Prop) (f : B -> B) (g : B -> B) (x : B) : (term703 B s f g x) = (term679 B s f g x).
Proof. exact (eq_refl (term703 B s f g x)). Qed.
Lemma lem5991113 {B : Type'} (s : B -> Prop) (f : B -> B) (g : B -> B) : (term704 B s f g) = (term685 B s f g).
Proof. exact (fun_ext (fun x : B => @lem5991112 B s f g x)). Qed.
Lemma lem5991114 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5991115 {B : Type'} (s : B -> Prop) (f : B -> B) (g : B -> B) : (term705 B s f g) = (term686 B s f g).
Proof. exact (MK_COMB (@lem5991114 B) (@lem5991113 B s f g)). Qed.
Lemma lem5991116 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5991117 {B : Type'} (s : B -> Prop) (f : B -> B) (g : B -> B) : (term706 B s f g) = (term688 B s f g).
Proof. exact (MK_COMB (@lem5991116) (@lem5991115 B s f g)). Qed.
Lemma lem5991118 {B : Type'} (f : B -> B) (op : type1400 B) (s : B -> Prop) (g : B -> B) : ((@iterate B B op s f) = (@iterate B B op s g)) = ((@iterate B B op s f) = (@iterate B B op s g)).
Proof. exact (eq_refl ((@iterate B B op s f) = (@iterate B B op s g))). Qed.
Lemma lem5991119 {B : Type'} (f : B -> B) (op : type1400 B) (s : B -> Prop) (g : B -> B) : (term701 B f op s g) = (term690 B f op s g).
Proof. exact (MK_COMB (@lem5991117 B s f g) (@lem5991118 B f op s g)). Qed.
Lemma lem5991120 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5991121 {B : Type'} (f : B -> B) (op : type1400 B) (s : B -> Prop) (g : B -> B) : (term707 B f op s g) = (term708 B f op s g).
Proof. exact (MK_COMB (@lem5991120) (@lem5991119 B f op s g)). Qed.
Lemma lem5991122 {B : Type'} (s : B -> Prop) (f : B -> B) (g : B -> B) (x : B) : (term703 B s f g x) = (term679 B s f g x).
Proof. exact (eq_refl (term703 B s f g x)). Qed.
Lemma lem5991123 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5991124 {B : Type'} (s : B -> Prop) (f : B -> B) (g : B -> B) (x : B) : (term709 B s f g x) = (term710 B s f g x).
Proof. exact (MK_COMB (@lem5991123) (@lem5991122 B s f g x)). Qed.
Lemma lem5991125 {B : Type'} (f : B -> B) (op : type1400 B) (s : B -> Prop) (g : B -> B) : ((@iterate B B op s f) = (@iterate B B op s g)) = ((@iterate B B op s f) = (@iterate B B op s g)).
Proof. exact (eq_refl ((@iterate B B op s f) = (@iterate B B op s g))). Qed.
Lemma lem5991126 {B : Type'} (x : B) (f : B -> B) (op : type1400 B) (s : B -> Prop) (g : B -> B) : (term711 B x f op s g) = (term712 B x f op s g).
Proof. exact (MK_COMB (@lem5991124 B s f g x) (@lem5991125 B f op s g)). Qed.
Lemma lem5991127 {B : Type'} (f : B -> B) (op : type1400 B) (s : B -> Prop) (g : B -> B) : (term713 B f op s g) = (term714 B f op s g).
Proof. exact (fun_ext (fun x : B => @lem5991126 B x f op s g)). Qed.
Lemma lem5991128 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5991129 {B : Type'} (f : B -> B) (op : type1400 B) (s : B -> Prop) (g : B -> B) : (term702 B f op s g) = (term715 B f op s g).
Proof. exact (MK_COMB (@lem5991128 B) (@lem5991127 B f op s g)). Qed.
Lemma lem5991130 {B : Type'} (f : B -> B) (op : type1400 B) (s : B -> Prop) (g : B -> B) : ((term701 B f op s g) = (term702 B f op s g)) = ((term690 B f op s g) = (term715 B f op s g)).
Proof. exact (MK_COMB (@lem5991121 B f op s g) (@lem5991129 B f op s g)). Qed.
Lemma lem5991131 {B : Type'} (f : B -> B) (op : type1400 B) (s : B -> Prop) (g : B -> B) : (term690 B f op s g) = (term715 B f op s g).
Proof. exact (EQ_MP (@lem5991130 B f op s g) (@lem5991111 B f op s g)). Qed.
Lemma lem5991132 {B : Type'} (f : B -> B) (op : type1400 B) (g : B -> B) : (term691 B f op g) = (term716 B f op g).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5991131 B f op s g)). Qed.
Lemma lem5991133 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5991134 {B : Type'} (f : B -> B) (op : type1400 B) (g : B -> B) : (term692 B f op g) = (term717 B f op g).
Proof. exact (MK_COMB (@lem5991133 B) (@lem5991132 B f op g)). Qed.
Lemma lem5991136 {A B : Type'} (P : type1413 A B) : (term186 A B P) = (term187 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5991137 {B : Type'} (P : type672 B) : (term564 B P) = (term565 B P).
Proof. exact (@lem5991136 (B -> Prop) B P). Qed.
Lemma lem5991138 {B : Type'} (f : B -> B) (op : type1400 B) (g : B -> B) : (term718 B f op g) = (term719 B f op g).
Proof. exact (@lem5991137 B (term720 B f op g)). Qed.
Lemma lem5991139 {B : Type'} (f : B -> B) (op : type1400 B) (s : B -> Prop) (g : B -> B) : (term721 B f op g s) = (term714 B f op s g).
Proof. exact (eq_refl (term721 B f op g s)). Qed.
Lemma lem5991140 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5991141 {B : Type'} (f : B -> B) (op : type1400 B) (s : B -> Prop) (g : B -> B) (x : B) : (term722 B f op g s x) = (term723 B f op s g x).
Proof. exact (MK_COMB (@lem5991139 B f op s g) (@lem5991140 B x)). Qed.
Lemma lem5991142 {B : Type'} (x : B) (f : B -> B) (op : type1400 B) (s : B -> Prop) (g : B -> B) : (term723 B f op s g x) = (term712 B x f op s g).
Proof. exact (eq_refl (term723 B f op s g x)). Qed.
Lemma lem5991143 {B : Type'} (x : B) (f : B -> B) (op : type1400 B) (s : B -> Prop) (g : B -> B) : (term722 B f op g s x) = (term712 B x f op s g).
Proof. exact (TRANS (@lem5991141 B f op s g x) (@lem5991142 B x f op s g)). Qed.
Lemma lem5991144 {B : Type'} (f : B -> B) (op : type1400 B) (s : B -> Prop) (g : B -> B) : (term724 B f op g s) = (term714 B f op s g).
Proof. exact (fun_ext (fun x : B => @lem5991143 B x f op s g)). Qed.
Lemma lem5991145 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5991146 {B : Type'} (f : B -> B) (op : type1400 B) (s : B -> Prop) (g : B -> B) : (term725 B f op g s) = (term715 B f op s g).
Proof. exact (MK_COMB (@lem5991145 B) (@lem5991144 B f op s g)). Qed.
Lemma lem5991147 {B : Type'} (f : B -> B) (op : type1400 B) (g : B -> B) : (term726 B f op g) = (term716 B f op g).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5991146 B f op s g)). Qed.
Lemma lem5991148 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5991149 {B : Type'} (f : B -> B) (op : type1400 B) (g : B -> B) : (term718 B f op g) = (term717 B f op g).
Proof. exact (MK_COMB (@lem5991148 B) (@lem5991147 B f op g)). Qed.
Lemma lem5991150 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5991151 {B : Type'} (f : B -> B) (op : type1400 B) (g : B -> B) : (term727 B f op g) = (term728 B f op g).
Proof. exact (MK_COMB (@lem5991150) (@lem5991149 B f op g)). Qed.
Lemma lem5991152 {B : Type'} (f : B -> B) (op : type1400 B) (s : B -> Prop) (g : B -> B) : (term721 B f op g s) = (term714 B f op s g).
Proof. exact (eq_refl (term721 B f op g s)). Qed.
Lemma lem5991153 {B : Type'} (x : type684 B) (s : B -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5991154 {B : Type'} (f : B -> B) (op : type1400 B) (g : B -> B) (x : type684 B) (s : B -> Prop) : (term729 B f op g x s) = (term730 B f op g x s).
Proof. exact (MK_COMB (@lem5991152 B f op s g) (@lem5991153 B x s)). Qed.
Lemma lem5991155 {B : Type'} (x : type684 B) (f : B -> B) (op : type1400 B) (s : B -> Prop) (g : B -> B) : (term730 B f op g x s) = (term731 B x f op s g).
Proof. exact (eq_refl (term730 B f op g x s)). Qed.
Lemma lem5991156 {B : Type'} (x : type684 B) (f : B -> B) (op : type1400 B) (s : B -> Prop) (g : B -> B) : (term729 B f op g x s) = (term731 B x f op s g).
Proof. exact (TRANS (@lem5991154 B f op g x s) (@lem5991155 B x f op s g)). Qed.
Lemma lem5991157 {B : Type'} (x : type684 B) (f : B -> B) (op : type1400 B) (g : B -> B) : (term732 B f op g x) = (term733 B x f op g).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5991156 B x f op s g)). Qed.
Lemma lem5991158 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5991159 {B : Type'} (x : type684 B) (f : B -> B) (op : type1400 B) (g : B -> B) : (term734 B f op g x) = (term735 B x f op g).
Proof. exact (MK_COMB (@lem5991158 B) (@lem5991157 B x f op g)). Qed.
Lemma lem5991160 {B : Type'} (f : B -> B) (op : type1400 B) (g : B -> B) : (term736 B f op g) = (term737 B f op g).
Proof. exact (fun_ext (fun x : type684 B => @lem5991159 B x f op g)). Qed.
Lemma lem5991161 {B : Type'} : (@ex ((B -> Prop) -> B)) = (@ex ((B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> B))). Qed.
Lemma lem5991162 {B : Type'} (f : B -> B) (op : type1400 B) (g : B -> B) : (term719 B f op g) = (term738 B f op g).
Proof. exact (MK_COMB (@lem5991161 B) (@lem5991160 B f op g)). Qed.
Lemma lem5991163 {B : Type'} (f : B -> B) (op : type1400 B) (g : B -> B) : ((term718 B f op g) = (term719 B f op g)) = ((term717 B f op g) = (term738 B f op g)).
Proof. exact (MK_COMB (@lem5991151 B f op g) (@lem5991162 B f op g)). Qed.
Lemma lem5991164 {B : Type'} (f : B -> B) (op : type1400 B) (g : B -> B) : (term717 B f op g) = (term738 B f op g).
Proof. exact (EQ_MP (@lem5991163 B f op g) (@lem5991138 B f op g)). Qed.
Lemma lem5991165 {B : Type'} (f : B -> B) (op : type1400 B) (g : B -> B) : (term692 B f op g) = (term738 B f op g).
Proof. exact (TRANS (@lem5991134 B f op g) (@lem5991164 B f op g)). Qed.
Lemma lem5991166 {B : Type'} (f : B -> B) (op : type1400 B) : (term693 B f op) = (term739 B f op).
Proof. exact (fun_ext (fun g : B -> B => @lem5991165 B f op g)). Qed.
Lemma lem5991167 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem5991168 {B : Type'} (f : B -> B) (op : type1400 B) : (term694 B f op) = (term740 B f op).
Proof. exact (MK_COMB (@lem5991167 B) (@lem5991166 B f op)). Qed.
Lemma lem5991170 {A B : Type'} (P : type1413 A B) : (term186 A B P) = (term187 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5991171 {B : Type'} (P : type481 B) : (term741 B P) = (term742 B P).
Proof. exact (@lem5991170 (B -> B) (type684 B) P). Qed.
Lemma lem5991172 {B : Type'} (f : B -> B) (op : type1400 B) : (term743 B f op) = (term744 B f op).
Proof. exact (@lem5991171 B (term745 B f op)). Qed.
Lemma lem5991173 {B : Type'} (f : B -> B) (op : type1400 B) (g : B -> B) : (term746 B f op g) = (term737 B f op g).
Proof. exact (eq_refl (term746 B f op g)). Qed.
Lemma lem5991174 {B : Type'} (x : type684 B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5991175 {B : Type'} (f : B -> B) (op : type1400 B) (g : B -> B) (x : type684 B) : (term747 B f op g x) = (term748 B f op g x).
Proof. exact (MK_COMB (@lem5991173 B f op g) (@lem5991174 B x)). Qed.
Lemma lem5991176 {B : Type'} (x : type684 B) (f : B -> B) (op : type1400 B) (g : B -> B) : (term748 B f op g x) = (term735 B x f op g).
Proof. exact (eq_refl (term748 B f op g x)). Qed.
Lemma lem5991177 {B : Type'} (x : type684 B) (f : B -> B) (op : type1400 B) (g : B -> B) : (term747 B f op g x) = (term735 B x f op g).
Proof. exact (TRANS (@lem5991175 B f op g x) (@lem5991176 B x f op g)). Qed.
Lemma lem5991178 {B : Type'} (f : B -> B) (op : type1400 B) (g : B -> B) : (term749 B f op g) = (term737 B f op g).
Proof. exact (fun_ext (fun x : type684 B => @lem5991177 B x f op g)). Qed.
Lemma lem5991179 {B : Type'} : (@ex ((B -> Prop) -> B)) = (@ex ((B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> B))). Qed.
Lemma lem5991180 {B : Type'} (f : B -> B) (op : type1400 B) (g : B -> B) : (term750 B f op g) = (term738 B f op g).
Proof. exact (MK_COMB (@lem5991179 B) (@lem5991178 B f op g)). Qed.
Lemma lem5991181 {B : Type'} (f : B -> B) (op : type1400 B) : (term751 B f op) = (term739 B f op).
Proof. exact (fun_ext (fun g : B -> B => @lem5991180 B f op g)). Qed.
Lemma lem5991182 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem5991183 {B : Type'} (f : B -> B) (op : type1400 B) : (term743 B f op) = (term740 B f op).
Proof. exact (MK_COMB (@lem5991182 B) (@lem5991181 B f op)). Qed.
Lemma lem5991184 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5991185 {B : Type'} (f : B -> B) (op : type1400 B) : (term752 B f op) = (term753 B f op).
Proof. exact (MK_COMB (@lem5991184) (@lem5991183 B f op)). Qed.
Lemma lem5991186 {B : Type'} (f : B -> B) (op : type1400 B) (g : B -> B) : (term746 B f op g) = (term737 B f op g).
Proof. exact (eq_refl (term746 B f op g)). Qed.
Lemma lem5991187 {B : Type'} (x : type485 B) (g : B -> B) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem5991188 {B : Type'} (f : B -> B) (op : type1400 B) (x : type485 B) (g : B -> B) : (term754 B f op x g) = (term755 B f op x g).
Proof. exact (MK_COMB (@lem5991186 B f op g) (@lem5991187 B x g)). Qed.
Lemma lem5991189 {B : Type'} (x : type485 B) (f : B -> B) (op : type1400 B) (g : B -> B) : (term755 B f op x g) = (term756 B x f op g).
Proof. exact (eq_refl (term755 B f op x g)). Qed.
Lemma lem5991190 {B : Type'} (x : type485 B) (f : B -> B) (op : type1400 B) (g : B -> B) : (term754 B f op x g) = (term756 B x f op g).
Proof. exact (TRANS (@lem5991188 B f op x g) (@lem5991189 B x f op g)). Qed.
Lemma lem5991191 {B : Type'} (x : type485 B) (f : B -> B) (op : type1400 B) : (term757 B f op x) = (term758 B x f op).
Proof. exact (fun_ext (fun g : B -> B => @lem5991190 B x f op g)). Qed.
Lemma lem5991192 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem5991193 {B : Type'} (x : type485 B) (f : B -> B) (op : type1400 B) : (term759 B f op x) = (term760 B x f op).
Proof. exact (MK_COMB (@lem5991192 B) (@lem5991191 B x f op)). Qed.
Lemma lem5991194 {B : Type'} (f : B -> B) (op : type1400 B) : (term761 B f op) = (term762 B f op).
Proof. exact (fun_ext (fun x : type485 B => @lem5991193 B x f op)). Qed.
Lemma lem5991195 {B : Type'} : (@ex ((B -> B) -> (B -> Prop) -> B)) = (@ex ((B -> B) -> (B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> B) -> (B -> Prop) -> B))). Qed.
Lemma lem5991196 {B : Type'} (f : B -> B) (op : type1400 B) : (term744 B f op) = (term763 B f op).
Proof. exact (MK_COMB (@lem5991195 B) (@lem5991194 B f op)). Qed.
Lemma lem5991197 {B : Type'} (f : B -> B) (op : type1400 B) : ((term743 B f op) = (term744 B f op)) = ((term740 B f op) = (term763 B f op)).
Proof. exact (MK_COMB (@lem5991185 B f op) (@lem5991196 B f op)). Qed.
Lemma lem5991198 {B : Type'} (f : B -> B) (op : type1400 B) : (term740 B f op) = (term763 B f op).
Proof. exact (EQ_MP (@lem5991197 B f op) (@lem5991172 B f op)). Qed.
Lemma lem5991199 {B : Type'} (f : B -> B) (op : type1400 B) : (term694 B f op) = (term763 B f op).
Proof. exact (TRANS (@lem5991168 B f op) (@lem5991198 B f op)). Qed.
Lemma lem5991200 {B : Type'} (op : type1400 B) : (term695 B op) = (term764 B op).
Proof. exact (fun_ext (fun f : B -> B => @lem5991199 B f op)). Qed.
Lemma lem5991201 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem5991202 {B : Type'} (op : type1400 B) : (term696 B op) = (term765 B op).
Proof. exact (MK_COMB (@lem5991201 B) (@lem5991200 B op)). Qed.
Lemma lem5991204 {A B : Type'} (P : type1413 A B) : (term186 A B P) = (term187 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5991205 {B : Type'} (P : type479 B) : (term766 B P) = (term767 B P).
Proof. exact (@lem5991204 (B -> B) (type485 B) P). Qed.
Lemma lem5991206 {B : Type'} (op : type1400 B) : (term768 B op) = (term769 B op).
Proof. exact (@lem5991205 B (term770 B op)). Qed.
Lemma lem5991207 {B : Type'} (f : B -> B) (op : type1400 B) : (term771 B op f) = (term762 B f op).
Proof. exact (eq_refl (term771 B op f)). Qed.
Lemma lem5991208 {B : Type'} (x : type485 B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5991209 {B : Type'} (f : B -> B) (op : type1400 B) (x : type485 B) : (term772 B op f x) = (term773 B f op x).
Proof. exact (MK_COMB (@lem5991207 B f op) (@lem5991208 B x)). Qed.
Lemma lem5991210 {B : Type'} (x : type485 B) (f : B -> B) (op : type1400 B) : (term773 B f op x) = (term760 B x f op).
Proof. exact (eq_refl (term773 B f op x)). Qed.
Lemma lem5991211 {B : Type'} (x : type485 B) (f : B -> B) (op : type1400 B) : (term772 B op f x) = (term760 B x f op).
Proof. exact (TRANS (@lem5991209 B f op x) (@lem5991210 B x f op)). Qed.
Lemma lem5991212 {B : Type'} (f : B -> B) (op : type1400 B) : (term774 B op f) = (term762 B f op).
Proof. exact (fun_ext (fun x : type485 B => @lem5991211 B x f op)). Qed.
Lemma lem5991213 {B : Type'} : (@ex ((B -> B) -> (B -> Prop) -> B)) = (@ex ((B -> B) -> (B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> B) -> (B -> Prop) -> B))). Qed.
Lemma lem5991214 {B : Type'} (f : B -> B) (op : type1400 B) : (term775 B op f) = (term763 B f op).
Proof. exact (MK_COMB (@lem5991213 B) (@lem5991212 B f op)). Qed.
Lemma lem5991215 {B : Type'} (op : type1400 B) : (term776 B op) = (term764 B op).
Proof. exact (fun_ext (fun f : B -> B => @lem5991214 B f op)). Qed.
Lemma lem5991216 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem5991217 {B : Type'} (op : type1400 B) : (term768 B op) = (term765 B op).
Proof. exact (MK_COMB (@lem5991216 B) (@lem5991215 B op)). Qed.
Lemma lem5991218 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5991219 {B : Type'} (op : type1400 B) : (term777 B op) = (term778 B op).
Proof. exact (MK_COMB (@lem5991218) (@lem5991217 B op)). Qed.
Lemma lem5991220 {B : Type'} (f : B -> B) (op : type1400 B) : (term771 B op f) = (term762 B f op).
Proof. exact (eq_refl (term771 B op f)). Qed.
Lemma lem5991221 {B : Type'} (x : type482 B) (f : B -> B) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem5991222 {B : Type'} (op : type1400 B) (x : type482 B) (f : B -> B) : (term779 B op x f) = (term780 B op x f).
Proof. exact (MK_COMB (@lem5991220 B f op) (@lem5991221 B x f)). Qed.
Lemma lem5991223 {B : Type'} (x : type482 B) (f : B -> B) (op : type1400 B) : (term780 B op x f) = (term781 B x f op).
Proof. exact (eq_refl (term780 B op x f)). Qed.
Lemma lem5991224 {B : Type'} (x : type482 B) (f : B -> B) (op : type1400 B) : (term779 B op x f) = (term781 B x f op).
Proof. exact (TRANS (@lem5991222 B op x f) (@lem5991223 B x f op)). Qed.
Lemma lem5991225 {B : Type'} (x : type482 B) (op : type1400 B) : (term782 B op x) = (term783 B x op).
Proof. exact (fun_ext (fun f : B -> B => @lem5991224 B x f op)). Qed.
Lemma lem5991226 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem5991227 {B : Type'} (x : type482 B) (op : type1400 B) : (term784 B op x) = (term785 B x op).
Proof. exact (MK_COMB (@lem5991226 B) (@lem5991225 B x op)). Qed.
Lemma lem5991228 {B : Type'} (op : type1400 B) : (term786 B op) = (term787 B op).
Proof. exact (fun_ext (fun x : type482 B => @lem5991227 B x op)). Qed.
Lemma lem5991229 {B : Type'} : (@ex ((B -> B) -> (B -> B) -> (B -> Prop) -> B)) = (@ex ((B -> B) -> (B -> B) -> (B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> B) -> (B -> B) -> (B -> Prop) -> B))). Qed.
Lemma lem5991230 {B : Type'} (op : type1400 B) : (term769 B op) = (term788 B op).
Proof. exact (MK_COMB (@lem5991229 B) (@lem5991228 B op)). Qed.
Lemma lem5991231 {B : Type'} (op : type1400 B) : ((term768 B op) = (term769 B op)) = ((term765 B op) = (term788 B op)).
Proof. exact (MK_COMB (@lem5991219 B op) (@lem5991230 B op)). Qed.
Lemma lem5991232 {B : Type'} (op : type1400 B) : (term765 B op) = (term788 B op).
Proof. exact (EQ_MP (@lem5991231 B op) (@lem5991206 B op)). Qed.
Lemma lem5991233 {B : Type'} (op : type1400 B) : (term696 B op) = (term788 B op).
Proof. exact (TRANS (@lem5991202 B op) (@lem5991232 B op)). Qed.
Lemma lem5991234 {B : Type'} (op : type1400 B) : (term540 B op) = (term540 B op).
Proof. exact (eq_refl (term540 B op)). Qed.
Lemma lem5991235 {B : Type'} (op : type1400 B) : (term698 B op) = (term789 B op).
Proof. exact (MK_COMB (@lem5991234 B op) (@lem5991233 B op)). Qed.
Lemma lem5991237 {A : Type'} (P : Prop) (Q : A -> Prop) : (term169 A P Q) = (term170 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5991238 {B : Type'} (P : Prop) (Q : type91 B) : (term790 B P Q) = (term791 B P Q).
Proof. exact (@lem5991237 (type482 B) P Q). Qed.
Lemma lem5991239 {B : Type'} (op : type1400 B) : (term792 B op) = (term793 B op).
Proof. exact (@lem5991238 B (term642 B op) (term787 B op)). Qed.
Lemma lem5991240 {B : Type'} (x : type482 B) (op : type1400 B) : (term794 B op x) = (term785 B x op).
Proof. exact (eq_refl (term794 B op x)). Qed.
Lemma lem5991241 {B : Type'} (op : type1400 B) : (term795 B op) = (term787 B op).
Proof. exact (fun_ext (fun x : type482 B => @lem5991240 B x op)). Qed.
Lemma lem5991242 {B : Type'} : (@ex ((B -> B) -> (B -> B) -> (B -> Prop) -> B)) = (@ex ((B -> B) -> (B -> B) -> (B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> B) -> (B -> B) -> (B -> Prop) -> B))). Qed.
Lemma lem5991243 {B : Type'} (op : type1400 B) : (term796 B op) = (term788 B op).
Proof. exact (MK_COMB (@lem5991242 B) (@lem5991241 B op)). Qed.
Lemma lem5991244 {B : Type'} (op : type1400 B) : (term540 B op) = (term540 B op).
Proof. exact (eq_refl (term540 B op)). Qed.
Lemma lem5991245 {B : Type'} (op : type1400 B) : (term792 B op) = (term789 B op).
Proof. exact (MK_COMB (@lem5991244 B op) (@lem5991243 B op)). Qed.
Lemma lem5991246 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5991247 {B : Type'} (op : type1400 B) : (term797 B op) = (term798 B op).
Proof. exact (MK_COMB (@lem5991246) (@lem5991245 B op)). Qed.
Lemma lem5991248 {B : Type'} (x : type482 B) (op : type1400 B) : (term794 B op x) = (term785 B x op).
Proof. exact (eq_refl (term794 B op x)). Qed.
Lemma lem5991249 {B : Type'} (op : type1400 B) : (term540 B op) = (term540 B op).
Proof. exact (eq_refl (term540 B op)). Qed.
Lemma lem5991250 {B : Type'} (x : type482 B) (op : type1400 B) : (term799 B op x) = (term800 B x op).
Proof. exact (MK_COMB (@lem5991249 B op) (@lem5991248 B x op)). Qed.
Lemma lem5991251 {B : Type'} (op : type1400 B) : (term801 B op) = (term802 B op).
Proof. exact (fun_ext (fun x : type482 B => @lem5991250 B x op)). Qed.
Lemma lem5991252 {B : Type'} : (@ex ((B -> B) -> (B -> B) -> (B -> Prop) -> B)) = (@ex ((B -> B) -> (B -> B) -> (B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> B) -> (B -> B) -> (B -> Prop) -> B))). Qed.
Lemma lem5991253 {B : Type'} (op : type1400 B) : (term793 B op) = (term803 B op).
Proof. exact (MK_COMB (@lem5991252 B) (@lem5991251 B op)). Qed.
Lemma lem5991254 {B : Type'} (op : type1400 B) : ((term792 B op) = (term793 B op)) = ((term789 B op) = (term803 B op)).
Proof. exact (MK_COMB (@lem5991247 B op) (@lem5991253 B op)). Qed.
Lemma lem5991255 {B : Type'} (op : type1400 B) : (term789 B op) = (term803 B op).
Proof. exact (EQ_MP (@lem5991254 B op) (@lem5991239 B op)). Qed.
Lemma lem5991256 {B : Type'} (op : type1400 B) : (term698 B op) = (term803 B op).
Proof. exact (TRANS (@lem5991235 B op) (@lem5991255 B op)). Qed.
Lemma lem5991257 {B : Type'} : (term699 B) = (term804 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5991256 B op)). Qed.
Lemma lem5991258 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5991259 {B : Type'} : (term700 B) = (term805 B).
Proof. exact (MK_COMB (@lem5991258 B) (@lem5991257 B)). Qed.
Lemma lem5991261 {A B : Type'} (P : type1413 A B) : (term186 A B P) = (term187 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5991262 {B : Type'} (P : type394 B) : (term806 B P) = (term807 B P).
Proof. exact (@lem5991261 (type1400 B) (type482 B) P). Qed.
Lemma lem5991263 {B : Type'} : (term808 B) = (term809 B).
Proof. exact (@lem5991262 B (term810 B)). Qed.
Lemma lem5991264 {B : Type'} (op : type1400 B) : (term811 B op) = (term802 B op).
Proof. exact (eq_refl (term811 B op)). Qed.
Lemma lem5991265 {B : Type'} (x : type482 B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5991266 {B : Type'} (op : type1400 B) (x : type482 B) : (term812 B op x) = (term813 B op x).
Proof. exact (MK_COMB (@lem5991264 B op) (@lem5991265 B x)). Qed.
Lemma lem5991267 {B : Type'} (x : type482 B) (op : type1400 B) : (term813 B op x) = (term800 B x op).
Proof. exact (eq_refl (term813 B op x)). Qed.
Lemma lem5991268 {B : Type'} (x : type482 B) (op : type1400 B) : (term812 B op x) = (term800 B x op).
Proof. exact (TRANS (@lem5991266 B op x) (@lem5991267 B x op)). Qed.
Lemma lem5991269 {B : Type'} (op : type1400 B) : (term814 B op) = (term802 B op).
Proof. exact (fun_ext (fun x : type482 B => @lem5991268 B x op)). Qed.
Lemma lem5991270 {B : Type'} : (@ex ((B -> B) -> (B -> B) -> (B -> Prop) -> B)) = (@ex ((B -> B) -> (B -> B) -> (B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> B) -> (B -> B) -> (B -> Prop) -> B))). Qed.
Lemma lem5991271 {B : Type'} (op : type1400 B) : (term815 B op) = (term803 B op).
Proof. exact (MK_COMB (@lem5991270 B) (@lem5991269 B op)). Qed.
Lemma lem5991272 {B : Type'} : (term816 B) = (term804 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5991271 B op)). Qed.
Lemma lem5991273 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5991274 {B : Type'} : (term808 B) = (term805 B).
Proof. exact (MK_COMB (@lem5991273 B) (@lem5991272 B)). Qed.
Lemma lem5991275 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5991276 {B : Type'} : (term817 B) = (term818 B).
Proof. exact (MK_COMB (@lem5991275) (@lem5991274 B)). Qed.
Lemma lem5991277 {B : Type'} (op : type1400 B) : (term811 B op) = (term802 B op).
Proof. exact (eq_refl (term811 B op)). Qed.
Lemma lem5991278 {B : Type'} (x : type396 B) (op : type1400 B) : (x op) = (x op).
Proof. exact (eq_refl (x op)). Qed.
Lemma lem5991279 {B : Type'} (x : type396 B) (op : type1400 B) : (term819 B x op) = (term820 B x op).
Proof. exact (MK_COMB (@lem5991277 B op) (@lem5991278 B x op)). Qed.
Lemma lem5991280 {B : Type'} (x : type396 B) (op : type1400 B) : (term820 B x op) = (term821 B x op).
Proof. exact (eq_refl (term820 B x op)). Qed.
Lemma lem5991281 {B : Type'} (x : type396 B) (op : type1400 B) : (term819 B x op) = (term821 B x op).
Proof. exact (TRANS (@lem5991279 B x op) (@lem5991280 B x op)). Qed.
Lemma lem5991282 {B : Type'} (x : type396 B) : (term822 B x) = (term823 B x).
Proof. exact (fun_ext (fun op : type1400 B => @lem5991281 B x op)). Qed.
Lemma lem5991283 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5991284 {B : Type'} (x : type396 B) : (term824 B x) = (term825 B x).
Proof. exact (MK_COMB (@lem5991283 B) (@lem5991282 B x)). Qed.
Lemma lem5991285 {B : Type'} : (term826 B) = (term827 B).
Proof. exact (fun_ext (fun x : type396 B => @lem5991284 B x)). Qed.
Lemma lem5991286 {B : Type'} : (@ex ((B -> B -> B) -> (B -> B) -> (B -> B) -> (B -> Prop) -> B)) = (@ex ((B -> B -> B) -> (B -> B) -> (B -> B) -> (B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> (B -> B) -> (B -> B) -> (B -> Prop) -> B))). Qed.
Lemma lem5991287 {B : Type'} : (term809 B) = (term828 B).
Proof. exact (MK_COMB (@lem5991286 B) (@lem5991285 B)). Qed.
Lemma lem5991288 {B : Type'} : ((term808 B) = (term809 B)) = ((term805 B) = (term828 B)).
Proof. exact (MK_COMB (@lem5991276 B) (@lem5991287 B)). Qed.
Lemma lem5991289 {B : Type'} : (term805 B) = (term828 B).
Proof. exact (EQ_MP (@lem5991288 B) (@lem5991263 B)). Qed.
Lemma lem5991291 {B : Type'} : (term700 B) = (term828 B).
Proof. exact (TRANS (@lem5991259 B) (@lem5991289 B)). Qed.
Lemma lem5991292 {B : Type'} : (term429 B) = (term828 B).
Proof. exact (TRANS (@lem5990954 B) (@lem5991291 B)). Qed.
Lemma lem5991293 {B : Type'} (h1 : term429 B) : term828 B.
Proof. exact (EQ_MP (@lem5991292 B) (@lem5989987 B h1)). Qed.
Lemma lem5991301 {A C : Type'} (s : A -> Prop) (f : A -> C) (g : A -> C) (x : A) : (term519 A C s f g x) = (term520 A C s f g x).
Proof. exact (@lem17362 (@IN A x s) ((f x) = (g x))). Qed.
Lemma lem5991302 {A : Type'} (P : A -> Prop) : (term521 A P) = (term522 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5991303 {A C : Type'} (s : A -> Prop) (f : A -> C) (g : A -> C) : (term523 A C s f g) = (term524 A C s f g).
Proof. exact (@lem5991302 A (term483 A C s f g)). Qed.
Lemma lem5991304 {A C : Type'} (s : A -> Prop) (f : A -> C) (g : A -> C) (x : A) : (term525 A C s f g x) = (term482 A C s f g x).
Proof. exact (eq_refl (term525 A C s f g x)). Qed.
Lemma lem5991305 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5991306 {A C : Type'} (s : A -> Prop) (f : A -> C) (g : A -> C) (x : A) : (term526 A C s f g x) = (term519 A C s f g x).
Proof. exact (MK_COMB (@lem5991305) (@lem5991304 A C s f g x)). Qed.
Lemma lem5991307 {A C : Type'} (s : A -> Prop) (f : A -> C) (g : A -> C) (x : A) : (term526 A C s f g x) = (term520 A C s f g x).
Proof. exact (TRANS (@lem5991306 A C s f g x) (@lem5991301 A C s f g x)). Qed.
Lemma lem5991308 {A C : Type'} (s : A -> Prop) (f : A -> C) (g : A -> C) : (term527 A C s f g) = (term528 A C s f g).
Proof. exact (fun_ext (fun x : A => @lem5991307 A C s f g x)). Qed.
Lemma lem5991309 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5991310 {A C : Type'} (s : A -> Prop) (f : A -> C) (g : A -> C) : (term524 A C s f g) = (term529 A C s f g).
Proof. exact (MK_COMB (@lem5991309 A) (@lem5991308 A C s f g)). Qed.
Lemma lem5991311 {A C : Type'} (s : A -> Prop) (f : A -> C) (g : A -> C) : (term523 A C s f g) = (term529 A C s f g).
Proof. exact (TRANS (@lem5991303 A C s f g) (@lem5991310 A C s f g)). Qed.
Lemma lem5991312 {A C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : ((@iterate C A op s f) = (@iterate C A op s g)) = ((@iterate C A op s f) = (@iterate C A op s g)).
Proof. exact (eq_refl ((@iterate C A op s f) = (@iterate C A op s g))). Qed.
Lemma lem5991313 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5991314 {A C : Type'} (s : A -> Prop) (f : A -> C) (g : A -> C) : (term530 A C s f g) = (term531 A C s f g).
Proof. exact (MK_COMB (@lem5991313) (@lem5991311 A C s f g)). Qed.
Lemma lem5991315 {A C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term532 A C f op s g) = (term533 A C f op s g).
Proof. exact (MK_COMB (@lem5991314 A C s f g) (@lem5991312 A C f op s g)). Qed.
Lemma lem5991316 {A C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term486 A C f op s g) = (term532 A C f op s g).
Proof. exact (@lem17265 (term484 A C s f g) ((@iterate C A op s f) = (@iterate C A op s g))). Qed.
Lemma lem5991317 {A C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term486 A C f op s g) = (term533 A C f op s g).
Proof. exact (TRANS (@lem5991316 A C f op s g) (@lem5991315 A C f op s g)). Qed.
Lemma lem5991318 {A C : Type'} (f : A -> C) (op : type1400 C) (g : A -> C) : (term487 A C f op g) = (term534 A C f op g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5991317 A C f op s g)). Qed.
Lemma lem5991319 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5991320 {A C : Type'} (f : A -> C) (op : type1400 C) (g : A -> C) : (term488 A C f op g) = (term535 A C f op g).
Proof. exact (MK_COMB (@lem5991319 A) (@lem5991318 A C f op g)). Qed.
Lemma lem5991321 {A C : Type'} (f : A -> C) (op : type1400 C) : (term489 A C f op) = (term536 A C f op).
Proof. exact (fun_ext (fun g : A -> C => @lem5991320 A C f op g)). Qed.
Lemma lem5991322 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem5991323 {A C : Type'} (f : A -> C) (op : type1400 C) : (term490 A C f op) = (term537 A C f op).
Proof. exact (MK_COMB (@lem5991322 A C) (@lem5991321 A C f op)). Qed.
Lemma lem5991324 {A C : Type'} (op : type1400 C) : (term491 A C op) = (term538 A C op).
Proof. exact (fun_ext (fun f : A -> C => @lem5991323 A C f op)). Qed.
Lemma lem5991325 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem5991326 {A C : Type'} (op : type1400 C) : (term492 A C op) = (term539 A C op).
Proof. exact (MK_COMB (@lem5991325 A C) (@lem5991324 A C op)). Qed.
Lemma lem5991328 {C : Type'} (op : type1400 C) : (term540 C op) = (term540 C op).
Proof. exact (eq_refl (term540 C op)). Qed.
Lemma lem5991329 {A C : Type'} (op : type1400 C) : (term541 A C op) = (term542 A C op).
Proof. exact (MK_COMB (@lem5991328 C op) (@lem5991326 A C op)). Qed.
Lemma lem5991330 {A C : Type'} (op : type1400 C) : (term493 A C op) = (term541 A C op).
Proof. exact (@lem17265 (@monoidal C op) (term492 A C op)). Qed.
Lemma lem5991331 {A C : Type'} (op : type1400 C) : (term493 A C op) = (term542 A C op).
Proof. exact (TRANS (@lem5991330 A C op) (@lem5991329 A C op)). Qed.
Lemma lem5991332 {A C : Type'} : (term494 A C) = (term543 A C).
Proof. exact (fun_ext (fun op : type1400 C => @lem5991331 A C op)). Qed.
Lemma lem5991333 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem5991334 {A C : Type'} : (term428 A C) = (term544 A C).
Proof. exact (MK_COMB (@lem5991333 C) (@lem5991332 A C)). Qed.
Lemma lem5991489 {A : Type'} (P : A -> Prop) (Q : Prop) : (term545 A P Q) = (term546 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5991490 {A : Type'} (P : A -> Prop) (Q : Prop) : (term545 A P Q) = (term546 A P Q).
Proof. exact (@lem5991489 A P Q). Qed.
Lemma lem5991491 {A C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term547 A C f op s g) = (term548 A C f op s g).
Proof. exact (@lem5991490 A (term528 A C s f g) ((@iterate C A op s f) = (@iterate C A op s g))). Qed.
Lemma lem5991492 {A C : Type'} (s : A -> Prop) (f : A -> C) (g : A -> C) (x : A) : (term549 A C s f g x) = (term520 A C s f g x).
Proof. exact (eq_refl (term549 A C s f g x)). Qed.
Lemma lem5991493 {A C : Type'} (s : A -> Prop) (f : A -> C) (g : A -> C) : (term550 A C s f g) = (term528 A C s f g).
Proof. exact (fun_ext (fun x : A => @lem5991492 A C s f g x)). Qed.
Lemma lem5991494 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5991495 {A C : Type'} (s : A -> Prop) (f : A -> C) (g : A -> C) : (term551 A C s f g) = (term529 A C s f g).
Proof. exact (MK_COMB (@lem5991494 A) (@lem5991493 A C s f g)). Qed.
Lemma lem5991496 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5991497 {A C : Type'} (s : A -> Prop) (f : A -> C) (g : A -> C) : (term552 A C s f g) = (term531 A C s f g).
Proof. exact (MK_COMB (@lem5991496) (@lem5991495 A C s f g)). Qed.
Lemma lem5991498 {A C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : ((@iterate C A op s f) = (@iterate C A op s g)) = ((@iterate C A op s f) = (@iterate C A op s g)).
Proof. exact (eq_refl ((@iterate C A op s f) = (@iterate C A op s g))). Qed.
Lemma lem5991499 {A C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term547 A C f op s g) = (term533 A C f op s g).
Proof. exact (MK_COMB (@lem5991497 A C s f g) (@lem5991498 A C f op s g)). Qed.
Lemma lem5991500 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5991501 {A C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term553 A C f op s g) = (term554 A C f op s g).
Proof. exact (MK_COMB (@lem5991500) (@lem5991499 A C f op s g)). Qed.
Lemma lem5991502 {A C : Type'} (s : A -> Prop) (f : A -> C) (g : A -> C) (x : A) : (term549 A C s f g x) = (term520 A C s f g x).
Proof. exact (eq_refl (term549 A C s f g x)). Qed.
Lemma lem5991503 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5991504 {A C : Type'} (s : A -> Prop) (f : A -> C) (g : A -> C) (x : A) : (term555 A C s f g x) = (term556 A C s f g x).
Proof. exact (MK_COMB (@lem5991503) (@lem5991502 A C s f g x)). Qed.
Lemma lem5991505 {A C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : ((@iterate C A op s f) = (@iterate C A op s g)) = ((@iterate C A op s f) = (@iterate C A op s g)).
Proof. exact (eq_refl ((@iterate C A op s f) = (@iterate C A op s g))). Qed.
Lemma lem5991506 {A C : Type'} (x : A) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term557 A C x f op s g) = (term558 A C x f op s g).
Proof. exact (MK_COMB (@lem5991504 A C s f g x) (@lem5991505 A C f op s g)). Qed.
Lemma lem5991507 {A C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term559 A C f op s g) = (term560 A C f op s g).
Proof. exact (fun_ext (fun x : A => @lem5991506 A C x f op s g)). Qed.
Lemma lem5991508 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5991509 {A C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term548 A C f op s g) = (term561 A C f op s g).
Proof. exact (MK_COMB (@lem5991508 A) (@lem5991507 A C f op s g)). Qed.
Lemma lem5991510 {A C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : ((term547 A C f op s g) = (term548 A C f op s g)) = ((term533 A C f op s g) = (term561 A C f op s g)).
Proof. exact (MK_COMB (@lem5991501 A C f op s g) (@lem5991509 A C f op s g)). Qed.
Lemma lem5991511 {A C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term533 A C f op s g) = (term561 A C f op s g).
Proof. exact (EQ_MP (@lem5991510 A C f op s g) (@lem5991491 A C f op s g)). Qed.
Lemma lem5991512 {A C : Type'} (f : A -> C) (op : type1400 C) (g : A -> C) : (term534 A C f op g) = (term562 A C f op g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5991511 A C f op s g)). Qed.
Lemma lem5991513 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5991514 {A C : Type'} (f : A -> C) (op : type1400 C) (g : A -> C) : (term535 A C f op g) = (term563 A C f op g).
Proof. exact (MK_COMB (@lem5991513 A) (@lem5991512 A C f op g)). Qed.
Lemma lem5991516 {A B : Type'} (P : type1413 A B) : (term186 A B P) = (term187 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5991517 {A : Type'} (P : type672 A) : (term564 A P) = (term565 A P).
Proof. exact (@lem5991516 (A -> Prop) A P). Qed.
Lemma lem5991518 {A C : Type'} (f : A -> C) (op : type1400 C) (g : A -> C) : (term566 A C f op g) = (term567 A C f op g).
Proof. exact (@lem5991517 A (term568 A C f op g)). Qed.
Lemma lem5991519 {A C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term569 A C f op g s) = (term560 A C f op s g).
Proof. exact (eq_refl (term569 A C f op g s)). Qed.
Lemma lem5991520 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5991521 {A C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) (x : A) : (term570 A C f op g s x) = (term571 A C f op s g x).
Proof. exact (MK_COMB (@lem5991519 A C f op s g) (@lem5991520 A x)). Qed.
Lemma lem5991522 {A C : Type'} (x : A) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term571 A C f op s g x) = (term558 A C x f op s g).
Proof. exact (eq_refl (term571 A C f op s g x)). Qed.
Lemma lem5991523 {A C : Type'} (x : A) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term570 A C f op g s x) = (term558 A C x f op s g).
Proof. exact (TRANS (@lem5991521 A C f op s g x) (@lem5991522 A C x f op s g)). Qed.
Lemma lem5991524 {A C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term572 A C f op g s) = (term560 A C f op s g).
Proof. exact (fun_ext (fun x : A => @lem5991523 A C x f op s g)). Qed.
Lemma lem5991525 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5991526 {A C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term573 A C f op g s) = (term561 A C f op s g).
Proof. exact (MK_COMB (@lem5991525 A) (@lem5991524 A C f op s g)). Qed.
Lemma lem5991527 {A C : Type'} (f : A -> C) (op : type1400 C) (g : A -> C) : (term574 A C f op g) = (term562 A C f op g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5991526 A C f op s g)). Qed.
Lemma lem5991528 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5991529 {A C : Type'} (f : A -> C) (op : type1400 C) (g : A -> C) : (term566 A C f op g) = (term563 A C f op g).
Proof. exact (MK_COMB (@lem5991528 A) (@lem5991527 A C f op g)). Qed.
Lemma lem5991530 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5991531 {A C : Type'} (f : A -> C) (op : type1400 C) (g : A -> C) : (term575 A C f op g) = (term576 A C f op g).
Proof. exact (MK_COMB (@lem5991530) (@lem5991529 A C f op g)). Qed.
Lemma lem5991532 {A C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term569 A C f op g s) = (term560 A C f op s g).
Proof. exact (eq_refl (term569 A C f op g s)). Qed.
Lemma lem5991533 {A : Type'} (x : type684 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5991534 {A C : Type'} (f : A -> C) (op : type1400 C) (g : A -> C) (x : type684 A) (s : A -> Prop) : (term577 A C f op g x s) = (term578 A C f op g x s).
Proof. exact (MK_COMB (@lem5991532 A C f op s g) (@lem5991533 A x s)). Qed.
Lemma lem5991535 {A C : Type'} (x : type684 A) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term578 A C f op g x s) = (term579 A C x f op s g).
Proof. exact (eq_refl (term578 A C f op g x s)). Qed.
Lemma lem5991536 {A C : Type'} (x : type684 A) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term577 A C f op g x s) = (term579 A C x f op s g).
Proof. exact (TRANS (@lem5991534 A C f op g x s) (@lem5991535 A C x f op s g)). Qed.
Lemma lem5991537 {A C : Type'} (x : type684 A) (f : A -> C) (op : type1400 C) (g : A -> C) : (term580 A C f op g x) = (term581 A C x f op g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5991536 A C x f op s g)). Qed.
Lemma lem5991538 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5991539 {A C : Type'} (x : type684 A) (f : A -> C) (op : type1400 C) (g : A -> C) : (term582 A C f op g x) = (term583 A C x f op g).
Proof. exact (MK_COMB (@lem5991538 A) (@lem5991537 A C x f op g)). Qed.
Lemma lem5991540 {A C : Type'} (f : A -> C) (op : type1400 C) (g : A -> C) : (term584 A C f op g) = (term585 A C f op g).
Proof. exact (fun_ext (fun x : type684 A => @lem5991539 A C x f op g)). Qed.
Lemma lem5991541 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem5991542 {A C : Type'} (f : A -> C) (op : type1400 C) (g : A -> C) : (term567 A C f op g) = (term586 A C f op g).
Proof. exact (MK_COMB (@lem5991541 A) (@lem5991540 A C f op g)). Qed.
Lemma lem5991543 {A C : Type'} (f : A -> C) (op : type1400 C) (g : A -> C) : ((term566 A C f op g) = (term567 A C f op g)) = ((term563 A C f op g) = (term586 A C f op g)).
Proof. exact (MK_COMB (@lem5991531 A C f op g) (@lem5991542 A C f op g)). Qed.
Lemma lem5991544 {A C : Type'} (f : A -> C) (op : type1400 C) (g : A -> C) : (term563 A C f op g) = (term586 A C f op g).
Proof. exact (EQ_MP (@lem5991543 A C f op g) (@lem5991518 A C f op g)). Qed.
Lemma lem5991545 {A C : Type'} (f : A -> C) (op : type1400 C) (g : A -> C) : (term535 A C f op g) = (term586 A C f op g).
Proof. exact (TRANS (@lem5991514 A C f op g) (@lem5991544 A C f op g)). Qed.
Lemma lem5991546 {A C : Type'} (f : A -> C) (op : type1400 C) : (term536 A C f op) = (term587 A C f op).
Proof. exact (fun_ext (fun g : A -> C => @lem5991545 A C f op g)). Qed.
Lemma lem5991547 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem5991548 {A C : Type'} (f : A -> C) (op : type1400 C) : (term537 A C f op) = (term588 A C f op).
Proof. exact (MK_COMB (@lem5991547 A C) (@lem5991546 A C f op)). Qed.
Lemma lem5991550 {A B : Type'} (P : type1413 A B) : (term186 A B P) = (term187 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5991551 {A C : Type'} (P : type503 A C) : (term589 A C P) = (term590 A C P).
Proof. exact (@lem5991550 (A -> C) (type684 A) P). Qed.
Lemma lem5991552 {A C : Type'} (f : A -> C) (op : type1400 C) : (term591 A C f op) = (term592 A C f op).
Proof. exact (@lem5991551 A C (term593 A C f op)). Qed.
Lemma lem5991553 {A C : Type'} (f : A -> C) (op : type1400 C) (g : A -> C) : (term594 A C f op g) = (term585 A C f op g).
Proof. exact (eq_refl (term594 A C f op g)). Qed.
Lemma lem5991554 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5991555 {A C : Type'} (f : A -> C) (op : type1400 C) (g : A -> C) (x : type684 A) : (term595 A C f op g x) = (term596 A C f op g x).
Proof. exact (MK_COMB (@lem5991553 A C f op g) (@lem5991554 A x)). Qed.
Lemma lem5991556 {A C : Type'} (x : type684 A) (f : A -> C) (op : type1400 C) (g : A -> C) : (term596 A C f op g x) = (term583 A C x f op g).
Proof. exact (eq_refl (term596 A C f op g x)). Qed.
Lemma lem5991557 {A C : Type'} (x : type684 A) (f : A -> C) (op : type1400 C) (g : A -> C) : (term595 A C f op g x) = (term583 A C x f op g).
Proof. exact (TRANS (@lem5991555 A C f op g x) (@lem5991556 A C x f op g)). Qed.
Lemma lem5991558 {A C : Type'} (f : A -> C) (op : type1400 C) (g : A -> C) : (term597 A C f op g) = (term585 A C f op g).
Proof. exact (fun_ext (fun x : type684 A => @lem5991557 A C x f op g)). Qed.
Lemma lem5991559 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem5991560 {A C : Type'} (f : A -> C) (op : type1400 C) (g : A -> C) : (term598 A C f op g) = (term586 A C f op g).
Proof. exact (MK_COMB (@lem5991559 A) (@lem5991558 A C f op g)). Qed.
Lemma lem5991561 {A C : Type'} (f : A -> C) (op : type1400 C) : (term599 A C f op) = (term587 A C f op).
Proof. exact (fun_ext (fun g : A -> C => @lem5991560 A C f op g)). Qed.
Lemma lem5991562 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem5991563 {A C : Type'} (f : A -> C) (op : type1400 C) : (term591 A C f op) = (term588 A C f op).
Proof. exact (MK_COMB (@lem5991562 A C) (@lem5991561 A C f op)). Qed.
Lemma lem5991564 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5991565 {A C : Type'} (f : A -> C) (op : type1400 C) : (term600 A C f op) = (term601 A C f op).
Proof. exact (MK_COMB (@lem5991564) (@lem5991563 A C f op)). Qed.
Lemma lem5991566 {A C : Type'} (f : A -> C) (op : type1400 C) (g : A -> C) : (term594 A C f op g) = (term585 A C f op g).
Proof. exact (eq_refl (term594 A C f op g)). Qed.
Lemma lem5991567 {A C : Type'} (x : type529 A C) (g : A -> C) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem5991568 {A C : Type'} (f : A -> C) (op : type1400 C) (x : type529 A C) (g : A -> C) : (term602 A C f op x g) = (term603 A C f op x g).
Proof. exact (MK_COMB (@lem5991566 A C f op g) (@lem5991567 A C x g)). Qed.
Lemma lem5991569 {A C : Type'} (x : type529 A C) (f : A -> C) (op : type1400 C) (g : A -> C) : (term603 A C f op x g) = (term604 A C x f op g).
Proof. exact (eq_refl (term603 A C f op x g)). Qed.
Lemma lem5991570 {A C : Type'} (x : type529 A C) (f : A -> C) (op : type1400 C) (g : A -> C) : (term602 A C f op x g) = (term604 A C x f op g).
Proof. exact (TRANS (@lem5991568 A C f op x g) (@lem5991569 A C x f op g)). Qed.
Lemma lem5991571 {A C : Type'} (x : type529 A C) (f : A -> C) (op : type1400 C) : (term605 A C f op x) = (term606 A C x f op).
Proof. exact (fun_ext (fun g : A -> C => @lem5991570 A C x f op g)). Qed.
Lemma lem5991572 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem5991573 {A C : Type'} (x : type529 A C) (f : A -> C) (op : type1400 C) : (term607 A C f op x) = (term608 A C x f op).
Proof. exact (MK_COMB (@lem5991572 A C) (@lem5991571 A C x f op)). Qed.
Lemma lem5991574 {A C : Type'} (f : A -> C) (op : type1400 C) : (term609 A C f op) = (term610 A C f op).
Proof. exact (fun_ext (fun x : type529 A C => @lem5991573 A C x f op)). Qed.
Lemma lem5991575 {A C : Type'} : (@ex ((A -> C) -> (A -> Prop) -> A)) = (@ex ((A -> C) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> C) -> (A -> Prop) -> A))). Qed.
Lemma lem5991576 {A C : Type'} (f : A -> C) (op : type1400 C) : (term592 A C f op) = (term611 A C f op).
Proof. exact (MK_COMB (@lem5991575 A C) (@lem5991574 A C f op)). Qed.
Lemma lem5991577 {A C : Type'} (f : A -> C) (op : type1400 C) : ((term591 A C f op) = (term592 A C f op)) = ((term588 A C f op) = (term611 A C f op)).
Proof. exact (MK_COMB (@lem5991565 A C f op) (@lem5991576 A C f op)). Qed.
Lemma lem5991578 {A C : Type'} (f : A -> C) (op : type1400 C) : (term588 A C f op) = (term611 A C f op).
Proof. exact (EQ_MP (@lem5991577 A C f op) (@lem5991552 A C f op)). Qed.
Lemma lem5991579 {A C : Type'} (f : A -> C) (op : type1400 C) : (term537 A C f op) = (term611 A C f op).
Proof. exact (TRANS (@lem5991548 A C f op) (@lem5991578 A C f op)). Qed.
Lemma lem5991580 {A C : Type'} (op : type1400 C) : (term538 A C op) = (term612 A C op).
Proof. exact (fun_ext (fun f : A -> C => @lem5991579 A C f op)). Qed.
Lemma lem5991581 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem5991582 {A C : Type'} (op : type1400 C) : (term539 A C op) = (term613 A C op).
Proof. exact (MK_COMB (@lem5991581 A C) (@lem5991580 A C op)). Qed.
Lemma lem5991584 {A B : Type'} (P : type1413 A B) : (term186 A B P) = (term187 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5991585 {A C : Type'} (P : type492 A C) : (term614 A C P) = (term615 A C P).
Proof. exact (@lem5991584 (A -> C) (type529 A C) P). Qed.
Lemma lem5991586 {A C : Type'} (op : type1400 C) : (term616 A C op) = (term617 A C op).
Proof. exact (@lem5991585 A C (term618 A C op)). Qed.
Lemma lem5991587 {A C : Type'} (f : A -> C) (op : type1400 C) : (term619 A C op f) = (term610 A C f op).
Proof. exact (eq_refl (term619 A C op f)). Qed.
Lemma lem5991588 {A C : Type'} (x : type529 A C) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5991589 {A C : Type'} (f : A -> C) (op : type1400 C) (x : type529 A C) : (term620 A C op f x) = (term621 A C f op x).
Proof. exact (MK_COMB (@lem5991587 A C f op) (@lem5991588 A C x)). Qed.
Lemma lem5991590 {A C : Type'} (x : type529 A C) (f : A -> C) (op : type1400 C) : (term621 A C f op x) = (term608 A C x f op).
Proof. exact (eq_refl (term621 A C f op x)). Qed.
Lemma lem5991591 {A C : Type'} (x : type529 A C) (f : A -> C) (op : type1400 C) : (term620 A C op f x) = (term608 A C x f op).
Proof. exact (TRANS (@lem5991589 A C f op x) (@lem5991590 A C x f op)). Qed.
Lemma lem5991592 {A C : Type'} (f : A -> C) (op : type1400 C) : (term622 A C op f) = (term610 A C f op).
Proof. exact (fun_ext (fun x : type529 A C => @lem5991591 A C x f op)). Qed.
Lemma lem5991593 {A C : Type'} : (@ex ((A -> C) -> (A -> Prop) -> A)) = (@ex ((A -> C) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> C) -> (A -> Prop) -> A))). Qed.
Lemma lem5991594 {A C : Type'} (f : A -> C) (op : type1400 C) : (term623 A C op f) = (term611 A C f op).
Proof. exact (MK_COMB (@lem5991593 A C) (@lem5991592 A C f op)). Qed.
Lemma lem5991595 {A C : Type'} (op : type1400 C) : (term624 A C op) = (term612 A C op).
Proof. exact (fun_ext (fun f : A -> C => @lem5991594 A C f op)). Qed.
Lemma lem5991596 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem5991597 {A C : Type'} (op : type1400 C) : (term616 A C op) = (term613 A C op).
Proof. exact (MK_COMB (@lem5991596 A C) (@lem5991595 A C op)). Qed.
Lemma lem5991598 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5991599 {A C : Type'} (op : type1400 C) : (term625 A C op) = (term626 A C op).
Proof. exact (MK_COMB (@lem5991598) (@lem5991597 A C op)). Qed.
Lemma lem5991600 {A C : Type'} (f : A -> C) (op : type1400 C) : (term619 A C op f) = (term610 A C f op).
Proof. exact (eq_refl (term619 A C op f)). Qed.
Lemma lem5991601 {A C : Type'} (x : type514 A C) (f : A -> C) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem5991602 {A C : Type'} (op : type1400 C) (x : type514 A C) (f : A -> C) : (term627 A C op x f) = (term628 A C op x f).
Proof. exact (MK_COMB (@lem5991600 A C f op) (@lem5991601 A C x f)). Qed.
Lemma lem5991603 {A C : Type'} (x : type514 A C) (f : A -> C) (op : type1400 C) : (term628 A C op x f) = (term629 A C x f op).
Proof. exact (eq_refl (term628 A C op x f)). Qed.
Lemma lem5991604 {A C : Type'} (x : type514 A C) (f : A -> C) (op : type1400 C) : (term627 A C op x f) = (term629 A C x f op).
Proof. exact (TRANS (@lem5991602 A C op x f) (@lem5991603 A C x f op)). Qed.
Lemma lem5991605 {A C : Type'} (x : type514 A C) (op : type1400 C) : (term630 A C op x) = (term631 A C x op).
Proof. exact (fun_ext (fun f : A -> C => @lem5991604 A C x f op)). Qed.
Lemma lem5991606 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem5991607 {A C : Type'} (x : type514 A C) (op : type1400 C) : (term632 A C op x) = (term633 A C x op).
Proof. exact (MK_COMB (@lem5991606 A C) (@lem5991605 A C x op)). Qed.
Lemma lem5991608 {A C : Type'} (op : type1400 C) : (term634 A C op) = (term635 A C op).
Proof. exact (fun_ext (fun x : type514 A C => @lem5991607 A C x op)). Qed.
Lemma lem5991609 {A C : Type'} : (@ex ((A -> C) -> (A -> C) -> (A -> Prop) -> A)) = (@ex ((A -> C) -> (A -> C) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> C) -> (A -> C) -> (A -> Prop) -> A))). Qed.
Lemma lem5991610 {A C : Type'} (op : type1400 C) : (term617 A C op) = (term636 A C op).
Proof. exact (MK_COMB (@lem5991609 A C) (@lem5991608 A C op)). Qed.
Lemma lem5991611 {A C : Type'} (op : type1400 C) : ((term616 A C op) = (term617 A C op)) = ((term613 A C op) = (term636 A C op)).
Proof. exact (MK_COMB (@lem5991599 A C op) (@lem5991610 A C op)). Qed.
Lemma lem5991612 {A C : Type'} (op : type1400 C) : (term613 A C op) = (term636 A C op).
Proof. exact (EQ_MP (@lem5991611 A C op) (@lem5991586 A C op)). Qed.
Lemma lem5991613 {A C : Type'} (op : type1400 C) : (term539 A C op) = (term636 A C op).
Proof. exact (TRANS (@lem5991582 A C op) (@lem5991612 A C op)). Qed.
Lemma lem5991614 {C : Type'} (op : type1400 C) : (term540 C op) = (term540 C op).
Proof. exact (eq_refl (term540 C op)). Qed.
Lemma lem5991615 {A C : Type'} (op : type1400 C) : (term542 A C op) = (term637 A C op).
Proof. exact (MK_COMB (@lem5991614 C op) (@lem5991613 A C op)). Qed.
Lemma lem5991617 {A : Type'} (P : Prop) (Q : A -> Prop) : (term169 A P Q) = (term170 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5991618 {A C : Type'} (P : Prop) (Q : type93 A C) : (term638 A C P Q) = (term639 A C P Q).
Proof. exact (@lem5991617 (type514 A C) P Q). Qed.
Lemma lem5991619 {A C : Type'} (op : type1400 C) : (term640 A C op) = (term641 A C op).
Proof. exact (@lem5991618 A C (term642 C op) (term635 A C op)). Qed.
Lemma lem5991620 {A C : Type'} (x : type514 A C) (op : type1400 C) : (term643 A C op x) = (term633 A C x op).
Proof. exact (eq_refl (term643 A C op x)). Qed.
Lemma lem5991621 {A C : Type'} (op : type1400 C) : (term644 A C op) = (term635 A C op).
Proof. exact (fun_ext (fun x : type514 A C => @lem5991620 A C x op)). Qed.
Lemma lem5991622 {A C : Type'} : (@ex ((A -> C) -> (A -> C) -> (A -> Prop) -> A)) = (@ex ((A -> C) -> (A -> C) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> C) -> (A -> C) -> (A -> Prop) -> A))). Qed.
Lemma lem5991623 {A C : Type'} (op : type1400 C) : (term645 A C op) = (term636 A C op).
Proof. exact (MK_COMB (@lem5991622 A C) (@lem5991621 A C op)). Qed.
Lemma lem5991624 {C : Type'} (op : type1400 C) : (term540 C op) = (term540 C op).
Proof. exact (eq_refl (term540 C op)). Qed.
Lemma lem5991625 {A C : Type'} (op : type1400 C) : (term640 A C op) = (term637 A C op).
Proof. exact (MK_COMB (@lem5991624 C op) (@lem5991623 A C op)). Qed.
Lemma lem5991626 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5991627 {A C : Type'} (op : type1400 C) : (term646 A C op) = (term647 A C op).
Proof. exact (MK_COMB (@lem5991626) (@lem5991625 A C op)). Qed.
Lemma lem5991628 {A C : Type'} (x : type514 A C) (op : type1400 C) : (term643 A C op x) = (term633 A C x op).
Proof. exact (eq_refl (term643 A C op x)). Qed.
Lemma lem5991629 {C : Type'} (op : type1400 C) : (term540 C op) = (term540 C op).
Proof. exact (eq_refl (term540 C op)). Qed.
Lemma lem5991630 {A C : Type'} (x : type514 A C) (op : type1400 C) : (term648 A C op x) = (term649 A C x op).
Proof. exact (MK_COMB (@lem5991629 C op) (@lem5991628 A C x op)). Qed.
Lemma lem5991631 {A C : Type'} (op : type1400 C) : (term650 A C op) = (term651 A C op).
Proof. exact (fun_ext (fun x : type514 A C => @lem5991630 A C x op)). Qed.
Lemma lem5991632 {A C : Type'} : (@ex ((A -> C) -> (A -> C) -> (A -> Prop) -> A)) = (@ex ((A -> C) -> (A -> C) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> C) -> (A -> C) -> (A -> Prop) -> A))). Qed.
Lemma lem5991633 {A C : Type'} (op : type1400 C) : (term641 A C op) = (term652 A C op).
Proof. exact (MK_COMB (@lem5991632 A C) (@lem5991631 A C op)). Qed.
Lemma lem5991634 {A C : Type'} (op : type1400 C) : ((term640 A C op) = (term641 A C op)) = ((term637 A C op) = (term652 A C op)).
Proof. exact (MK_COMB (@lem5991627 A C op) (@lem5991633 A C op)). Qed.
Lemma lem5991635 {A C : Type'} (op : type1400 C) : (term637 A C op) = (term652 A C op).
Proof. exact (EQ_MP (@lem5991634 A C op) (@lem5991619 A C op)). Qed.
Lemma lem5991636 {A C : Type'} (op : type1400 C) : (term542 A C op) = (term652 A C op).
Proof. exact (TRANS (@lem5991615 A C op) (@lem5991635 A C op)). Qed.
Lemma lem5991637 {A C : Type'} : (term543 A C) = (term653 A C).
Proof. exact (fun_ext (fun op : type1400 C => @lem5991636 A C op)). Qed.
Lemma lem5991638 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem5991639 {A C : Type'} : (term544 A C) = (term654 A C).
Proof. exact (MK_COMB (@lem5991638 C) (@lem5991637 A C)). Qed.
Lemma lem5991641 {A B : Type'} (P : type1413 A B) : (term186 A B P) = (term187 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5991642 {A C : Type'} (P : type746 A C) : (term655 A C P) = (term656 A C P).
Proof. exact (@lem5991641 (type1400 C) (type514 A C) P). Qed.
Lemma lem5991643 {A C : Type'} : (term657 A C) = (term658 A C).
Proof. exact (@lem5991642 A C (term659 A C)). Qed.
Lemma lem5991644 {A C : Type'} (op : type1400 C) : (term660 A C op) = (term651 A C op).
Proof. exact (eq_refl (term660 A C op)). Qed.
Lemma lem5991645 {A C : Type'} (x : type514 A C) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5991646 {A C : Type'} (op : type1400 C) (x : type514 A C) : (term661 A C op x) = (term662 A C op x).
Proof. exact (MK_COMB (@lem5991644 A C op) (@lem5991645 A C x)). Qed.
Lemma lem5991647 {A C : Type'} (x : type514 A C) (op : type1400 C) : (term662 A C op x) = (term649 A C x op).
Proof. exact (eq_refl (term662 A C op x)). Qed.
Lemma lem5991648 {A C : Type'} (x : type514 A C) (op : type1400 C) : (term661 A C op x) = (term649 A C x op).
Proof. exact (TRANS (@lem5991646 A C op x) (@lem5991647 A C x op)). Qed.
Lemma lem5991649 {A C : Type'} (op : type1400 C) : (term663 A C op) = (term651 A C op).
Proof. exact (fun_ext (fun x : type514 A C => @lem5991648 A C x op)). Qed.
Lemma lem5991650 {A C : Type'} : (@ex ((A -> C) -> (A -> C) -> (A -> Prop) -> A)) = (@ex ((A -> C) -> (A -> C) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> C) -> (A -> C) -> (A -> Prop) -> A))). Qed.
Lemma lem5991651 {A C : Type'} (op : type1400 C) : (term664 A C op) = (term652 A C op).
Proof. exact (MK_COMB (@lem5991650 A C) (@lem5991649 A C op)). Qed.
Lemma lem5991652 {A C : Type'} : (term665 A C) = (term653 A C).
Proof. exact (fun_ext (fun op : type1400 C => @lem5991651 A C op)). Qed.
Lemma lem5991653 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem5991654 {A C : Type'} : (term657 A C) = (term654 A C).
Proof. exact (MK_COMB (@lem5991653 C) (@lem5991652 A C)). Qed.
Lemma lem5991655 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5991656 {A C : Type'} : (term666 A C) = (term667 A C).
Proof. exact (MK_COMB (@lem5991655) (@lem5991654 A C)). Qed.
Lemma lem5991657 {A C : Type'} (op : type1400 C) : (term660 A C op) = (term651 A C op).
Proof. exact (eq_refl (term660 A C op)). Qed.
Lemma lem5991658 {A C : Type'} (x : type747 A C) (op : type1400 C) : (x op) = (x op).
Proof. exact (eq_refl (x op)). Qed.
Lemma lem5991659 {A C : Type'} (x : type747 A C) (op : type1400 C) : (term668 A C x op) = (term669 A C x op).
Proof. exact (MK_COMB (@lem5991657 A C op) (@lem5991658 A C x op)). Qed.
Lemma lem5991660 {A C : Type'} (x : type747 A C) (op : type1400 C) : (term669 A C x op) = (term670 A C x op).
Proof. exact (eq_refl (term669 A C x op)). Qed.
Lemma lem5991661 {A C : Type'} (x : type747 A C) (op : type1400 C) : (term668 A C x op) = (term670 A C x op).
Proof. exact (TRANS (@lem5991659 A C x op) (@lem5991660 A C x op)). Qed.
Lemma lem5991662 {A C : Type'} (x : type747 A C) : (term671 A C x) = (term672 A C x).
Proof. exact (fun_ext (fun op : type1400 C => @lem5991661 A C x op)). Qed.
Lemma lem5991663 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem5991664 {A C : Type'} (x : type747 A C) : (term673 A C x) = (term674 A C x).
Proof. exact (MK_COMB (@lem5991663 C) (@lem5991662 A C x)). Qed.
Lemma lem5991665 {A C : Type'} : (term675 A C) = (term676 A C).
Proof. exact (fun_ext (fun x : type747 A C => @lem5991664 A C x)). Qed.
Lemma lem5991666 {A C : Type'} : (@ex ((C -> C -> C) -> (A -> C) -> (A -> C) -> (A -> Prop) -> A)) = (@ex ((C -> C -> C) -> (A -> C) -> (A -> C) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((C -> C -> C) -> (A -> C) -> (A -> C) -> (A -> Prop) -> A))). Qed.
Lemma lem5991667 {A C : Type'} : (term658 A C) = (term677 A C).
Proof. exact (MK_COMB (@lem5991666 A C) (@lem5991665 A C)). Qed.
Lemma lem5991668 {A C : Type'} : ((term657 A C) = (term658 A C)) = ((term654 A C) = (term677 A C)).
Proof. exact (MK_COMB (@lem5991656 A C) (@lem5991667 A C)). Qed.
Lemma lem5991669 {A C : Type'} : (term654 A C) = (term677 A C).
Proof. exact (EQ_MP (@lem5991668 A C) (@lem5991643 A C)). Qed.
Lemma lem5991671 {A C : Type'} : (term544 A C) = (term677 A C).
Proof. exact (TRANS (@lem5991639 A C) (@lem5991669 A C)). Qed.
Lemma lem5991672 {A C : Type'} : (term428 A C) = (term677 A C).
Proof. exact (TRANS (@lem5991334 A C) (@lem5991671 A C)). Qed.
Lemma lem5991673 {A C : Type'} (h1 : term428 A C) : term677 A C.
Proof. exact (EQ_MP (@lem5991672 A C) (@lem5989988 A C h1)). Qed.
Lemma lem5991674 {A C : Type'} (x : type747 A C) (h1 : term674 A C x) : term674 A C x.
Proof. exact (h1). Qed.
Lemma lem5991682 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5991683 {C : Type'} (f : type403 C) (x : type1400 C) : (f x) = (@I ((C -> C -> C) -> Prop) f x).
Proof. exact (@lem5991682 (type1400 C) Prop f x). Qed.
Lemma lem5991685 {C : Type'} (op : type1400 C) : (@monoidal C op) = (@I ((C -> C -> C) -> Prop) (@monoidal C) op).
Proof. exact (@lem5991683 C (@monoidal C) op). Qed.
Lemma lem5991687 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem5991688 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem5991693 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5991694 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5991693 A B f x). Qed.
Lemma lem5991696 {A B : Type'} (h : A -> B) (x : A) : (h x) = (@I (A -> B) h x).
Proof. exact (@lem5991694 A B h x). Qed.
Lemma lem5991697 {A B C : Type'} (g : B -> C) (h : A -> B) (x : A) : (term341 A B C g h x) = (term829 A B C g h x).
Proof. exact (MK_COMB (@lem5991688 B C g) (@lem5991696 A B h x)). Qed.
Lemma lem5991699 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5991700 {B C : Type'} (f : B -> C) (x : B) : (f x) = (@I (B -> C) f x).
Proof. exact (@lem5991699 B C f x). Qed.
Lemma lem5991701 {A B C : Type'} (g : B -> C) (h : A -> B) (x : A) : (term829 A B C g h x) = (term830 A B C g h x).
Proof. exact (@lem5991700 B C g (@I (A -> B) h x)). Qed.
Lemma lem5991702 {A B C : Type'} (g : B -> C) (h : A -> B) (x : A) : (term341 A B C g h x) = (term830 A B C g h x).
Proof. exact (TRANS (@lem5991697 A B C g h x) (@lem5991701 A B C g h x)). Qed.
Lemma lem5991707 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5991709 {A C : Type'} (f : A -> C) (x : A) : (f x) = (@I (A -> C) f x).
Proof. exact (@lem5991707 A C f x). Qed.
Lemma lem5991710 {A B C : Type'} (g : B -> C) (h : A -> B) (x : A) : (term831 A B C g h x) = (term832 A B C g h x).
Proof. exact (MK_COMB (@lem5991687 C) (@lem5991702 A B C g h x)). Qed.
Lemma lem5991711 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : ((term341 A B C g h x) = (f x)) = ((term830 A B C g h x) = (@I (A -> C) f x)).
Proof. exact (MK_COMB (@lem5991710 A B C g h x) (@lem5991709 A C f x)). Qed.
Lemma lem5991712 {B : Type'} : (@IN B) = (@IN B).
Proof. exact (eq_refl (@IN B)). Qed.
Lemma lem5991717 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5991718 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5991717 A B f x). Qed.
Lemma lem5991720 {A B : Type'} (h : A -> B) (x : A) : (h x) = (@I (A -> B) h x).
Proof. exact (@lem5991718 A B h x). Qed.
Lemma lem5991721 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5991722 {A B : Type'} (h : A -> B) (x : A) : (term833 A B h x) = (term834 A B h x).
Proof. exact (MK_COMB (@lem5991712 B) (@lem5991720 A B h x)). Qed.
Lemma lem5991723 {A B : Type'} (h : A -> B) (x : A) (t : B -> Prop) : (term340 A B h x t) = (term835 A B h x t).
Proof. exact (MK_COMB (@lem5991722 A B h x) (@lem5991721 B t)). Qed.
Lemma lem5991725 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5991726 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem5991725 B (type686 B) f x). Qed.
Lemma lem5991727 {A B : Type'} (h : A -> B) (x : A) : (term834 A B h x) = (term836 A B h x).
Proof. exact (@lem5991726 B (@IN B) (@I (A -> B) h x)). Qed.
Lemma lem5991728 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5991729 {A B : Type'} (h : A -> B) (x : A) (t : B -> Prop) : (term835 A B h x t) = (term837 A B h x t).
Proof. exact (MK_COMB (@lem5991727 A B h x) (@lem5991728 B t)). Qed.
Lemma lem5991731 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5991732 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem5991731 (B -> Prop) Prop f x). Qed.
Lemma lem5991733 {A B : Type'} (h : A -> B) (x : A) (t : B -> Prop) : (term837 A B h x t) = (term838 A B h x t).
Proof. exact (@lem5991732 B (term836 A B h x) t). Qed.
Lemma lem5991734 {A B : Type'} (h : A -> B) (x : A) (t : B -> Prop) : (term835 A B h x t) = (term838 A B h x t).
Proof. exact (TRANS (@lem5991729 A B h x t) (@lem5991733 A B h x t)). Qed.
Lemma lem5991735 {A B : Type'} (h : A -> B) (x : A) (t : B -> Prop) : (term340 A B h x t) = (term838 A B h x t).
Proof. exact (TRANS (@lem5991723 A B h x t) (@lem5991734 A B h x t)). Qed.
Lemma lem5991736 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5991737 {A B : Type'} (h : A -> B) (x : A) (t : B -> Prop) : (term839 A B h x t) = (term840 A B h x t).
Proof. exact (MK_COMB (@lem5991736) (@lem5991735 A B h x t)). Qed.
Lemma lem5991738 {A B C : Type'} (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term212 A B C t g h f x) = (term841 A B C t g h f x).
Proof. exact (MK_COMB (@lem5991737 A B h x t) (@lem5991711 A B C g h f x)). Qed.
Lemma lem5991739 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5991746 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5991747 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5991746 A (type686 A) f x). Qed.
Lemma lem5991748 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5991747 A (@IN A) x). Qed.
Lemma lem5991749 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5991750 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem5991748 A x) (@lem5991749 A s)). Qed.
Lemma lem5991752 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5991753 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5991752 (A -> Prop) Prop f x). Qed.
Lemma lem5991754 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term842 A x s).
Proof. exact (@lem5991753 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem5991756 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term842 A x s).
Proof. exact (TRANS (@lem5991750 A x s) (@lem5991754 A x s)). Qed.
Lemma lem5991757 {A : Type'} (x : A) (s : A -> Prop) : (term173 A x s) = (term843 A x s).
Proof. exact (MK_COMB (@lem5991739) (@lem5991756 A x s)). Qed.
Lemma lem5991758 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5991759 {A : Type'} (x : A) (s : A -> Prop) : (term130 A x s) = (term844 A x s).
Proof. exact (MK_COMB (@lem5991758) (@lem5991757 A x s)). Qed.
Lemma lem5991760 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term211 A B C s t g h f x) = (term845 A B C s t g h f x).
Proof. exact (MK_COMB (@lem5991759 A x s) (@lem5991738 A B C t g h f x)). Qed.
Lemma lem5991761 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term213 A B C s t g h f) = (term846 A B C s t g h f).
Proof. exact (fun_ext (fun x : A => @lem5991760 A B C s t g h f x)). Qed.
Lemma lem5991762 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5991763 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term214 A B C s t g h f) = (term847 A B C s t g h f).
Proof. exact (MK_COMB (@lem5991762 A) (@lem5991761 A B C s t g h f)). Qed.
Lemma lem5991764 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term847 A B C s t g h f.
Proof. exact (EQ_MP (@lem5991763 A B C s t g h f) (@lem5990473 A B C s t g h f h1)). Qed.
Lemma lem5991765 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5991766 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem5991775 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5991776 {A C : Type'} (f : type750 A C) (x : type1400 C) : (f x) = (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) f x).
Proof. exact (@lem5991775 (type1400 C) (type632 A C) f x). Qed.
Lemma lem5991777 {A C : Type'} (op : type1400 C) : (@iterate C A op) = (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) (@iterate C A) op).
Proof. exact (@lem5991776 A C (@iterate C A) op). Qed.
Lemma lem5991778 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5991779 {A C : Type'} (op : type1400 C) (s : A -> Prop) : (@iterate C A op s) = (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) (@iterate C A) op s).
Proof. exact (MK_COMB (@lem5991777 A C op) (@lem5991778 A s)). Qed.
Lemma lem5991781 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5991782 {A C : Type'} (f : type632 A C) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> C) -> C) f x).
Proof. exact (@lem5991781 (A -> Prop) (type570 A C) f x). Qed.
Lemma lem5991783 {A C : Type'} (op : type1400 C) (s : A -> Prop) : (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) (@iterate C A) op s) = (term848 A C op s).
Proof. exact (@lem5991782 A C (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) (@iterate C A) op) s). Qed.
Lemma lem5991784 {A C : Type'} (op : type1400 C) (s : A -> Prop) : (@iterate C A op s) = (term848 A C op s).
Proof. exact (TRANS (@lem5991779 A C op s) (@lem5991783 A C op s)). Qed.
Lemma lem5991785 {A C : Type'} (f : A -> C) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5991786 {A C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> C) : (@iterate C A op s f) = (term849 A C op s f).
Proof. exact (MK_COMB (@lem5991784 A C op s) (@lem5991785 A C f)). Qed.
Lemma lem5991788 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5991789 {A C : Type'} (f : type570 A C) (x : A -> C) : (f x) = (@I ((A -> C) -> C) f x).
Proof. exact (@lem5991788 (A -> C) C f x). Qed.
Lemma lem5991790 {A C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> C) : (term849 A C op s f) = (term850 A C op s f).
Proof. exact (@lem5991789 A C (term848 A C op s) f). Qed.
Lemma lem5991792 {A C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> C) : (@iterate C A op s f) = (term850 A C op s f).
Proof. exact (TRANS (@lem5991786 A C op s f) (@lem5991790 A C op s f)). Qed.
Lemma lem5991802 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5991803 {A B C : Type'} (f : type808 A B C) (x : B -> C) : (f x) = (@I ((B -> C) -> (A -> B) -> A -> C) f x).
Proof. exact (@lem5991802 (B -> C) (type550 A B C) f x). Qed.
Lemma lem5991804 {A B C : Type'} (g : B -> C) : (@o A B C g) = (@I ((B -> C) -> (A -> B) -> A -> C) (@o A B C) g).
Proof. exact (@lem5991803 A B C (@o A B C) g). Qed.
Lemma lem5991805 {A B : Type'} (h : A -> B) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem5991806 {A B C : Type'} (g : B -> C) (h : A -> B) : (@o A B C g h) = (@I ((B -> C) -> (A -> B) -> A -> C) (@o A B C) g h).
Proof. exact (MK_COMB (@lem5991804 A B C g) (@lem5991805 A B h)). Qed.
Lemma lem5991808 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5991809 {A B C : Type'} (f : type550 A B C) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> C) f x).
Proof. exact (@lem5991808 (A -> B) (A -> C) f x). Qed.
Lemma lem5991810 {A B C : Type'} (g : B -> C) (h : A -> B) : (@I ((B -> C) -> (A -> B) -> A -> C) (@o A B C) g h) = (term851 A B C g h).
Proof. exact (@lem5991809 A B C (@I ((B -> C) -> (A -> B) -> A -> C) (@o A B C) g) h). Qed.
Lemma lem5991812 {A B C : Type'} (g : B -> C) (h : A -> B) : (@o A B C g h) = (term851 A B C g h).
Proof. exact (TRANS (@lem5991806 A B C g h) (@lem5991810 A B C g h)). Qed.
Lemma lem5991814 {A C : Type'} (op : type1400 C) (s : A -> Prop) : (@iterate C A op s) = (@iterate C A op s).
Proof. exact (eq_refl (@iterate C A op s)). Qed.
Lemma lem5991815 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term425 A B C op s g h) = (term852 A B C op s g h).
Proof. exact (MK_COMB (@lem5991814 A C op s) (@lem5991812 A B C g h)). Qed.
Lemma lem5991817 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5991818 {A C : Type'} (f : type750 A C) (x : type1400 C) : (f x) = (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) f x).
Proof. exact (@lem5991817 (type1400 C) (type632 A C) f x). Qed.
Lemma lem5991819 {A C : Type'} (op : type1400 C) : (@iterate C A op) = (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) (@iterate C A) op).
Proof. exact (@lem5991818 A C (@iterate C A) op). Qed.
Lemma lem5991820 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5991821 {A C : Type'} (op : type1400 C) (s : A -> Prop) : (@iterate C A op s) = (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) (@iterate C A) op s).
Proof. exact (MK_COMB (@lem5991819 A C op) (@lem5991820 A s)). Qed.
Lemma lem5991823 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5991824 {A C : Type'} (f : type632 A C) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> C) -> C) f x).
Proof. exact (@lem5991823 (A -> Prop) (type570 A C) f x). Qed.
Lemma lem5991825 {A C : Type'} (op : type1400 C) (s : A -> Prop) : (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) (@iterate C A) op s) = (term848 A C op s).
Proof. exact (@lem5991824 A C (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) (@iterate C A) op) s). Qed.
Lemma lem5991826 {A C : Type'} (op : type1400 C) (s : A -> Prop) : (@iterate C A op s) = (term848 A C op s).
Proof. exact (TRANS (@lem5991821 A C op s) (@lem5991825 A C op s)). Qed.
Lemma lem5991827 {A B C : Type'} (g : B -> C) (h : A -> B) : (term851 A B C g h) = (term851 A B C g h).
Proof. exact (eq_refl (term851 A B C g h)). Qed.
Lemma lem5991828 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term852 A B C op s g h) = (term853 A B C op s g h).
Proof. exact (MK_COMB (@lem5991826 A C op s) (@lem5991827 A B C g h)). Qed.
Lemma lem5991830 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5991831 {A C : Type'} (f : type570 A C) (x : A -> C) : (f x) = (@I ((A -> C) -> C) f x).
Proof. exact (@lem5991830 (A -> C) C f x). Qed.
Lemma lem5991832 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term853 A B C op s g h) = (term854 A B C op s g h).
Proof. exact (@lem5991831 A C (term848 A C op s) (term851 A B C g h)). Qed.
Lemma lem5991833 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term852 A B C op s g h) = (term854 A B C op s g h).
Proof. exact (TRANS (@lem5991828 A B C op s g h) (@lem5991832 A B C op s g h)). Qed.
Lemma lem5991834 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term425 A B C op s g h) = (term854 A B C op s g h).
Proof. exact (TRANS (@lem5991815 A B C op s g h) (@lem5991833 A B C op s g h)). Qed.
Lemma lem5991835 {A C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> C) : (term855 A C op s f) = (term856 A C op s f).
Proof. exact (MK_COMB (@lem5991766 C) (@lem5991792 A C op s f)). Qed.
Lemma lem5991836 {A B C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : ((@iterate C A op s f) = (term425 A B C op s g h)) = ((term850 A C op s f) = (term854 A B C op s g h)).
Proof. exact (MK_COMB (@lem5991835 A C op s f) (@lem5991834 A B C op s g h)). Qed.
Lemma lem5991837 {A B C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term427 A B C f op s g h) = (term857 A B C f op s g h).
Proof. exact (MK_COMB (@lem5991765) (@lem5991836 A B C f op s g h)). Qed.
Lemma lem5991893 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem5991902 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5991903 {A B C : Type'} (f : type808 A B C) (x : B -> C) : (f x) = (@I ((B -> C) -> (A -> B) -> A -> C) f x).
Proof. exact (@lem5991902 (B -> C) (type550 A B C) f x). Qed.
Lemma lem5991904 {A B C : Type'} (f : B -> C) : (@o A B C f) = (@I ((B -> C) -> (A -> B) -> A -> C) (@o A B C) f).
Proof. exact (@lem5991903 A B C (@o A B C) f). Qed.
Lemma lem5991905 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem5991906 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (@I ((B -> C) -> (A -> B) -> A -> C) (@o A B C) f g).
Proof. exact (MK_COMB (@lem5991904 A B C f) (@lem5991905 A B g)). Qed.
Lemma lem5991908 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5991909 {A B C : Type'} (f : type550 A B C) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> C) f x).
Proof. exact (@lem5991908 (A -> B) (A -> C) f x). Qed.
Lemma lem5991910 {A B C : Type'} (f : B -> C) (g : A -> B) : (@I ((B -> C) -> (A -> B) -> A -> C) (@o A B C) f g) = (term851 A B C f g).
Proof. exact (@lem5991909 A B C (@I ((B -> C) -> (A -> B) -> A -> C) (@o A B C) f) g). Qed.
Lemma lem5991911 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term851 A B C f g).
Proof. exact (TRANS (@lem5991906 A B C f g) (@lem5991910 A B C f g)). Qed.
Lemma lem5991912 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5991913 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (@o A B C f g x) = (term858 A B C f g x).
Proof. exact (MK_COMB (@lem5991911 A B C f g) (@lem5991912 A x)). Qed.
Lemma lem5991915 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5991916 {A C : Type'} (f : A -> C) (x : A) : (f x) = (@I (A -> C) f x).
Proof. exact (@lem5991915 A C f x). Qed.
Lemma lem5991917 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (term858 A B C f g x) = (term859 A B C f g x).
Proof. exact (@lem5991916 A C (term851 A B C f g) x). Qed.
Lemma lem5991919 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (@o A B C f g x) = (term859 A B C f g x).
Proof. exact (TRANS (@lem5991913 A B C f g x) (@lem5991917 A B C f g x)). Qed.
Lemma lem5991920 {B C : Type'} (f : B -> C) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5991925 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5991926 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5991925 A B f x). Qed.
Lemma lem5991928 {A B : Type'} (g : A -> B) (x : A) : (g x) = (@I (A -> B) g x).
Proof. exact (@lem5991926 A B g x). Qed.
Lemma lem5991929 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (term341 A B C f g x) = (term829 A B C f g x).
Proof. exact (MK_COMB (@lem5991920 B C f) (@lem5991928 A B g x)). Qed.
Lemma lem5991931 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5991932 {B C : Type'} (f : B -> C) (x : B) : (f x) = (@I (B -> C) f x).
Proof. exact (@lem5991931 B C f x). Qed.
Lemma lem5991933 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (term829 A B C f g x) = (term830 A B C f g x).
Proof. exact (@lem5991932 B C f (@I (A -> B) g x)). Qed.
Lemma lem5991934 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (term341 A B C f g x) = (term830 A B C f g x).
Proof. exact (TRANS (@lem5991929 A B C f g x) (@lem5991933 A B C f g x)). Qed.
Lemma lem5991935 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (term860 A B C f g x) = (term861 A B C f g x).
Proof. exact (MK_COMB (@lem5991893 C) (@lem5991919 A B C f g x)). Qed.
Lemma lem5991936 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : ((@o A B C f g x) = (term341 A B C f g x)) = ((term859 A B C f g x) = (term830 A B C f g x)).
Proof. exact (MK_COMB (@lem5991935 A B C f g x) (@lem5991934 A B C f g x)). Qed.
Lemma lem5991937 {A B C : Type'} (f : B -> C) (g : A -> B) : (term508 A B C f g) = (term862 A B C f g).
Proof. exact (fun_ext (fun x : A => @lem5991936 A B C f g x)). Qed.
Lemma lem5991938 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5991939 {A B C : Type'} (f : B -> C) (g : A -> B) : (term509 A B C f g) = (term863 A B C f g).
Proof. exact (MK_COMB (@lem5991938 A) (@lem5991937 A B C f g)). Qed.
Lemma lem5991940 {A B C : Type'} (f : B -> C) : (term510 A B C f) = (term864 A B C f).
Proof. exact (fun_ext (fun g : A -> B => @lem5991939 A B C f g)). Qed.
Lemma lem5991941 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5991942 {A B C : Type'} (f : B -> C) : (term511 A B C f) = (term865 A B C f).
Proof. exact (MK_COMB (@lem5991941 A B) (@lem5991940 A B C f)). Qed.
Lemma lem5991943 {A B C : Type'} : (term512 A B C) = (term866 A B C).
Proof. exact (fun_ext (fun f : B -> C => @lem5991942 A B C f)). Qed.
Lemma lem5991944 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem5991945 {A B C : Type'} : (term431 A B C) = (term867 A B C).
Proof. exact (MK_COMB (@lem5991944 B C) (@lem5991943 A B C)). Qed.
Lemma lem5991946 {A B C : Type'} (h1 : term431 A B C) : term867 A B C.
Proof. exact (EQ_MP (@lem5991945 A B C) (@lem5990533 A B C h1)). Qed.
Lemma lem5991947 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem5991956 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5991957 {A C : Type'} (f : type750 A C) (x : type1400 C) : (f x) = (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) f x).
Proof. exact (@lem5991956 (type1400 C) (type632 A C) f x). Qed.
Lemma lem5991958 {A C : Type'} (op : type1400 C) : (@iterate C A op) = (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) (@iterate C A) op).
Proof. exact (@lem5991957 A C (@iterate C A) op). Qed.
Lemma lem5991959 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5991960 {A C : Type'} (op : type1400 C) (s : A -> Prop) : (@iterate C A op s) = (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) (@iterate C A) op s).
Proof. exact (MK_COMB (@lem5991958 A C op) (@lem5991959 A s)). Qed.
Lemma lem5991962 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5991963 {A C : Type'} (f : type632 A C) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> C) -> C) f x).
Proof. exact (@lem5991962 (A -> Prop) (type570 A C) f x). Qed.
Lemma lem5991964 {A C : Type'} (op : type1400 C) (s : A -> Prop) : (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) (@iterate C A) op s) = (term848 A C op s).
Proof. exact (@lem5991963 A C (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) (@iterate C A) op) s). Qed.
Lemma lem5991965 {A C : Type'} (op : type1400 C) (s : A -> Prop) : (@iterate C A op s) = (term848 A C op s).
Proof. exact (TRANS (@lem5991960 A C op s) (@lem5991964 A C op s)). Qed.
Lemma lem5991966 {A C : Type'} (f : A -> C) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5991967 {A C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> C) : (@iterate C A op s f) = (term849 A C op s f).
Proof. exact (MK_COMB (@lem5991965 A C op s) (@lem5991966 A C f)). Qed.
Lemma lem5991969 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5991970 {A C : Type'} (f : type570 A C) (x : A -> C) : (f x) = (@I ((A -> C) -> C) f x).
Proof. exact (@lem5991969 (A -> C) C f x). Qed.
Lemma lem5991971 {A C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> C) : (term849 A C op s f) = (term850 A C op s f).
Proof. exact (@lem5991970 A C (term848 A C op s) f). Qed.
Lemma lem5991973 {A C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> C) : (@iterate C A op s f) = (term850 A C op s f).
Proof. exact (TRANS (@lem5991967 A C op s f) (@lem5991971 A C op s f)). Qed.
Lemma lem5991982 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5991983 {A C : Type'} (f : type750 A C) (x : type1400 C) : (f x) = (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) f x).
Proof. exact (@lem5991982 (type1400 C) (type632 A C) f x). Qed.
Lemma lem5991984 {A C : Type'} (op : type1400 C) : (@iterate C A op) = (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) (@iterate C A) op).
Proof. exact (@lem5991983 A C (@iterate C A) op). Qed.
Lemma lem5991985 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5991986 {A C : Type'} (op : type1400 C) (s : A -> Prop) : (@iterate C A op s) = (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) (@iterate C A) op s).
Proof. exact (MK_COMB (@lem5991984 A C op) (@lem5991985 A s)). Qed.
Lemma lem5991988 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5991989 {A C : Type'} (f : type632 A C) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> C) -> C) f x).
Proof. exact (@lem5991988 (A -> Prop) (type570 A C) f x). Qed.
Lemma lem5991990 {A C : Type'} (op : type1400 C) (s : A -> Prop) : (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) (@iterate C A) op s) = (term848 A C op s).
Proof. exact (@lem5991989 A C (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) (@iterate C A) op) s). Qed.
Lemma lem5991991 {A C : Type'} (op : type1400 C) (s : A -> Prop) : (@iterate C A op s) = (term848 A C op s).
Proof. exact (TRANS (@lem5991986 A C op s) (@lem5991990 A C op s)). Qed.
Lemma lem5991992 {A C : Type'} (g : A -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem5991993 {A C : Type'} (op : type1400 C) (s : A -> Prop) (g : A -> C) : (@iterate C A op s g) = (term849 A C op s g).
Proof. exact (MK_COMB (@lem5991991 A C op s) (@lem5991992 A C g)). Qed.
Lemma lem5991995 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5991996 {A C : Type'} (f : type570 A C) (x : A -> C) : (f x) = (@I ((A -> C) -> C) f x).
Proof. exact (@lem5991995 (A -> C) C f x). Qed.
Lemma lem5991997 {A C : Type'} (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term849 A C op s g) = (term850 A C op s g).
Proof. exact (@lem5991996 A C (term848 A C op s) g). Qed.
Lemma lem5991999 {A C : Type'} (op : type1400 C) (s : A -> Prop) (g : A -> C) : (@iterate C A op s g) = (term850 A C op s g).
Proof. exact (TRANS (@lem5991993 A C op s g) (@lem5991997 A C op s g)). Qed.
Lemma lem5992000 {A C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> C) : (term855 A C op s f) = (term856 A C op s f).
Proof. exact (MK_COMB (@lem5991947 C) (@lem5991973 A C op s f)). Qed.
Lemma lem5992001 {A C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : ((@iterate C A op s f) = (@iterate C A op s g)) = ((term850 A C op s f) = (term850 A C op s g)).
Proof. exact (MK_COMB (@lem5992000 A C op s f) (@lem5991999 A C op s g)). Qed.
Lemma lem5992002 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5992003 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem5992004 {A C : Type'} (f : A -> C) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5992015 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5992016 {A C : Type'} (f : type747 A C) (x : type1400 C) : (f x) = (@I ((C -> C -> C) -> (A -> C) -> (A -> C) -> (A -> Prop) -> A) f x).
Proof. exact (@lem5992015 (type1400 C) (type514 A C) f x). Qed.
Lemma lem5992017 {A C : Type'} (x : type747 A C) (op : type1400 C) : (x op) = (@I ((C -> C -> C) -> (A -> C) -> (A -> C) -> (A -> Prop) -> A) x op).
Proof. exact (@lem5992016 A C x op). Qed.
Lemma lem5992018 {A C : Type'} (f : A -> C) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5992019 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) : (x op f) = (@I ((C -> C -> C) -> (A -> C) -> (A -> C) -> (A -> Prop) -> A) x op f).
Proof. exact (MK_COMB (@lem5992017 A C x op) (@lem5992018 A C f)). Qed.
Lemma lem5992021 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5992022 {A C : Type'} (f : type514 A C) (x : A -> C) : (f x) = (@I ((A -> C) -> (A -> C) -> (A -> Prop) -> A) f x).
Proof. exact (@lem5992021 (A -> C) (type529 A C) f x). Qed.
Lemma lem5992023 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) : (@I ((C -> C -> C) -> (A -> C) -> (A -> C) -> (A -> Prop) -> A) x op f) = (term868 A C x op f).
Proof. exact (@lem5992022 A C (@I ((C -> C -> C) -> (A -> C) -> (A -> C) -> (A -> Prop) -> A) x op) f). Qed.
Lemma lem5992024 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) : (x op f) = (term868 A C x op f).
Proof. exact (TRANS (@lem5992019 A C x op f) (@lem5992023 A C x op f)). Qed.
Lemma lem5992025 {A C : Type'} (g : A -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem5992026 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) : (x op f g) = (term869 A C x op f g).
Proof. exact (MK_COMB (@lem5992024 A C x op f) (@lem5992025 A C g)). Qed.
Lemma lem5992028 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5992029 {A C : Type'} (f : type529 A C) (x : A -> C) : (f x) = (@I ((A -> C) -> (A -> Prop) -> A) f x).
Proof. exact (@lem5992028 (A -> C) (type684 A) f x). Qed.
Lemma lem5992030 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) : (term869 A C x op f g) = (term870 A C x op f g).
Proof. exact (@lem5992029 A C (term868 A C x op f) g). Qed.
Lemma lem5992031 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) : (x op f g) = (term870 A C x op f g).
Proof. exact (TRANS (@lem5992026 A C x op f g) (@lem5992030 A C x op f g)). Qed.
Lemma lem5992032 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5992033 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) (s : A -> Prop) : (x op f g s) = (term871 A C x op f g s).
Proof. exact (MK_COMB (@lem5992031 A C x op f g) (@lem5992032 A s)). Qed.
Lemma lem5992035 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5992036 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem5992035 (A -> Prop) A f x). Qed.
Lemma lem5992037 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) (s : A -> Prop) : (term871 A C x op f g s) = (term872 A C x op f g s).
Proof. exact (@lem5992036 A (term870 A C x op f g) s). Qed.
Lemma lem5992039 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) (s : A -> Prop) : (x op f g s) = (term872 A C x op f g s).
Proof. exact (TRANS (@lem5992033 A C x op f g s) (@lem5992037 A C x op f g s)). Qed.
Lemma lem5992040 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) (s : A -> Prop) : (term873 A C x op f g s) = (term874 A C x op f g s).
Proof. exact (MK_COMB (@lem5992004 A C f) (@lem5992039 A C x op f g s)). Qed.
Lemma lem5992042 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5992043 {A C : Type'} (f : A -> C) (x : A) : (f x) = (@I (A -> C) f x).
Proof. exact (@lem5992042 A C f x). Qed.
Lemma lem5992044 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) (s : A -> Prop) : (term874 A C x op f g s) = (term875 A C x op f g s).
Proof. exact (@lem5992043 A C f (term872 A C x op f g s)). Qed.
Lemma lem5992045 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) (s : A -> Prop) : (term873 A C x op f g s) = (term875 A C x op f g s).
Proof. exact (TRANS (@lem5992040 A C x op f g s) (@lem5992044 A C x op f g s)). Qed.
Lemma lem5992046 {A C : Type'} (g : A -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem5992057 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5992058 {A C : Type'} (f : type747 A C) (x : type1400 C) : (f x) = (@I ((C -> C -> C) -> (A -> C) -> (A -> C) -> (A -> Prop) -> A) f x).
Proof. exact (@lem5992057 (type1400 C) (type514 A C) f x). Qed.
Lemma lem5992059 {A C : Type'} (x : type747 A C) (op : type1400 C) : (x op) = (@I ((C -> C -> C) -> (A -> C) -> (A -> C) -> (A -> Prop) -> A) x op).
Proof. exact (@lem5992058 A C x op). Qed.
Lemma lem5992060 {A C : Type'} (f : A -> C) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5992061 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) : (x op f) = (@I ((C -> C -> C) -> (A -> C) -> (A -> C) -> (A -> Prop) -> A) x op f).
Proof. exact (MK_COMB (@lem5992059 A C x op) (@lem5992060 A C f)). Qed.
Lemma lem5992063 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5992064 {A C : Type'} (f : type514 A C) (x : A -> C) : (f x) = (@I ((A -> C) -> (A -> C) -> (A -> Prop) -> A) f x).
Proof. exact (@lem5992063 (A -> C) (type529 A C) f x). Qed.
Lemma lem5992065 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) : (@I ((C -> C -> C) -> (A -> C) -> (A -> C) -> (A -> Prop) -> A) x op f) = (term868 A C x op f).
Proof. exact (@lem5992064 A C (@I ((C -> C -> C) -> (A -> C) -> (A -> C) -> (A -> Prop) -> A) x op) f). Qed.
Lemma lem5992066 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) : (x op f) = (term868 A C x op f).
Proof. exact (TRANS (@lem5992061 A C x op f) (@lem5992065 A C x op f)). Qed.
Lemma lem5992067 {A C : Type'} (g : A -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem5992068 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) : (x op f g) = (term869 A C x op f g).
Proof. exact (MK_COMB (@lem5992066 A C x op f) (@lem5992067 A C g)). Qed.
Lemma lem5992070 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5992071 {A C : Type'} (f : type529 A C) (x : A -> C) : (f x) = (@I ((A -> C) -> (A -> Prop) -> A) f x).
Proof. exact (@lem5992070 (A -> C) (type684 A) f x). Qed.
Lemma lem5992072 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) : (term869 A C x op f g) = (term870 A C x op f g).
Proof. exact (@lem5992071 A C (term868 A C x op f) g). Qed.
Lemma lem5992073 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) : (x op f g) = (term870 A C x op f g).
Proof. exact (TRANS (@lem5992068 A C x op f g) (@lem5992072 A C x op f g)). Qed.
Lemma lem5992074 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5992075 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) (s : A -> Prop) : (x op f g s) = (term871 A C x op f g s).
Proof. exact (MK_COMB (@lem5992073 A C x op f g) (@lem5992074 A s)). Qed.
Lemma lem5992077 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5992078 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem5992077 (A -> Prop) A f x). Qed.
Lemma lem5992079 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) (s : A -> Prop) : (term871 A C x op f g s) = (term872 A C x op f g s).
Proof. exact (@lem5992078 A (term870 A C x op f g) s). Qed.
Lemma lem5992081 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) (s : A -> Prop) : (x op f g s) = (term872 A C x op f g s).
Proof. exact (TRANS (@lem5992075 A C x op f g s) (@lem5992079 A C x op f g s)). Qed.
Lemma lem5992082 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) (s : A -> Prop) : (term876 A C x op f g s) = (term877 A C x op f g s).
Proof. exact (MK_COMB (@lem5992046 A C g) (@lem5992081 A C x op f g s)). Qed.
Lemma lem5992084 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5992085 {A C : Type'} (f : A -> C) (x : A) : (f x) = (@I (A -> C) f x).
Proof. exact (@lem5992084 A C f x). Qed.
Lemma lem5992086 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) (s : A -> Prop) : (term877 A C x op f g s) = (term878 A C x op f g s).
Proof. exact (@lem5992085 A C g (term872 A C x op f g s)). Qed.
Lemma lem5992087 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) (s : A -> Prop) : (term876 A C x op f g s) = (term878 A C x op f g s).
Proof. exact (TRANS (@lem5992082 A C x op f g s) (@lem5992086 A C x op f g s)). Qed.
Lemma lem5992088 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) (s : A -> Prop) : (term879 A C x op f g s) = (term880 A C x op f g s).
Proof. exact (MK_COMB (@lem5992003 C) (@lem5992045 A C x op f g s)). Qed.
Lemma lem5992089 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) (s : A -> Prop) : ((term873 A C x op f g s) = (term876 A C x op f g s)) = ((term875 A C x op f g s) = (term878 A C x op f g s)).
Proof. exact (MK_COMB (@lem5992088 A C x op f g s) (@lem5992087 A C x op f g s)). Qed.
Lemma lem5992090 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) (s : A -> Prop) : (term881 A C x op f g s) = (term882 A C x op f g s).
Proof. exact (MK_COMB (@lem5992002) (@lem5992089 A C x op f g s)). Qed.
Lemma lem5992091 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem5992102 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5992103 {A C : Type'} (f : type747 A C) (x : type1400 C) : (f x) = (@I ((C -> C -> C) -> (A -> C) -> (A -> C) -> (A -> Prop) -> A) f x).
Proof. exact (@lem5992102 (type1400 C) (type514 A C) f x). Qed.
Lemma lem5992104 {A C : Type'} (x : type747 A C) (op : type1400 C) : (x op) = (@I ((C -> C -> C) -> (A -> C) -> (A -> C) -> (A -> Prop) -> A) x op).
Proof. exact (@lem5992103 A C x op). Qed.
Lemma lem5992105 {A C : Type'} (f : A -> C) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5992106 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) : (x op f) = (@I ((C -> C -> C) -> (A -> C) -> (A -> C) -> (A -> Prop) -> A) x op f).
Proof. exact (MK_COMB (@lem5992104 A C x op) (@lem5992105 A C f)). Qed.
Lemma lem5992108 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5992109 {A C : Type'} (f : type514 A C) (x : A -> C) : (f x) = (@I ((A -> C) -> (A -> C) -> (A -> Prop) -> A) f x).
Proof. exact (@lem5992108 (A -> C) (type529 A C) f x). Qed.
Lemma lem5992110 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) : (@I ((C -> C -> C) -> (A -> C) -> (A -> C) -> (A -> Prop) -> A) x op f) = (term868 A C x op f).
Proof. exact (@lem5992109 A C (@I ((C -> C -> C) -> (A -> C) -> (A -> C) -> (A -> Prop) -> A) x op) f). Qed.
Lemma lem5992111 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) : (x op f) = (term868 A C x op f).
Proof. exact (TRANS (@lem5992106 A C x op f) (@lem5992110 A C x op f)). Qed.
Lemma lem5992112 {A C : Type'} (g : A -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem5992113 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) : (x op f g) = (term869 A C x op f g).
Proof. exact (MK_COMB (@lem5992111 A C x op f) (@lem5992112 A C g)). Qed.
Lemma lem5992115 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5992116 {A C : Type'} (f : type529 A C) (x : A -> C) : (f x) = (@I ((A -> C) -> (A -> Prop) -> A) f x).
Proof. exact (@lem5992115 (A -> C) (type684 A) f x). Qed.
Lemma lem5992117 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) : (term869 A C x op f g) = (term870 A C x op f g).
Proof. exact (@lem5992116 A C (term868 A C x op f) g). Qed.
Lemma lem5992118 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) : (x op f g) = (term870 A C x op f g).
Proof. exact (TRANS (@lem5992113 A C x op f g) (@lem5992117 A C x op f g)). Qed.
Lemma lem5992119 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5992120 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) (s : A -> Prop) : (x op f g s) = (term871 A C x op f g s).
Proof. exact (MK_COMB (@lem5992118 A C x op f g) (@lem5992119 A s)). Qed.
Lemma lem5992122 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5992123 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem5992122 (A -> Prop) A f x). Qed.
Lemma lem5992124 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) (s : A -> Prop) : (term871 A C x op f g s) = (term872 A C x op f g s).
Proof. exact (@lem5992123 A (term870 A C x op f g) s). Qed.
Lemma lem5992126 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) (s : A -> Prop) : (x op f g s) = (term872 A C x op f g s).
Proof. exact (TRANS (@lem5992120 A C x op f g s) (@lem5992124 A C x op f g s)). Qed.
Lemma lem5992127 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5992128 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) (s : A -> Prop) : (term883 A C x op f g s) = (term884 A C x op f g s).
Proof. exact (MK_COMB (@lem5992091 A) (@lem5992126 A C x op f g s)). Qed.
Lemma lem5992129 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) (s : A -> Prop) : (term885 A C x op f g s) = (term886 A C x op f g s).
Proof. exact (MK_COMB (@lem5992128 A C x op f g s) (@lem5992127 A s)). Qed.
Lemma lem5992131 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5992132 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5992131 A (type686 A) f x). Qed.
Lemma lem5992133 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) (s : A -> Prop) : (term884 A C x op f g s) = (term887 A C x op f g s).
Proof. exact (@lem5992132 A (@IN A) (term872 A C x op f g s)). Qed.
Lemma lem5992134 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5992135 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) (s : A -> Prop) : (term886 A C x op f g s) = (term888 A C x op f g s).
Proof. exact (MK_COMB (@lem5992133 A C x op f g s) (@lem5992134 A s)). Qed.
Lemma lem5992137 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5992138 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5992137 (A -> Prop) Prop f x). Qed.
Lemma lem5992139 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) (s : A -> Prop) : (term888 A C x op f g s) = (term889 A C x op f g s).
Proof. exact (@lem5992138 A (term887 A C x op f g s) s). Qed.
Lemma lem5992140 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) (s : A -> Prop) : (term886 A C x op f g s) = (term889 A C x op f g s).
Proof. exact (TRANS (@lem5992135 A C x op f g s) (@lem5992139 A C x op f g s)). Qed.
Lemma lem5992141 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) (s : A -> Prop) : (term885 A C x op f g s) = (term889 A C x op f g s).
Proof. exact (TRANS (@lem5992129 A C x op f g s) (@lem5992140 A C x op f g s)). Qed.
Lemma lem5992142 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5992143 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) (s : A -> Prop) : (term890 A C x op f g s) = (term891 A C x op f g s).
Proof. exact (MK_COMB (@lem5992142) (@lem5992141 A C x op f g s)). Qed.
Lemma lem5992144 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) (s : A -> Prop) : (term892 A C x op f g s) = (term893 A C x op f g s).
Proof. exact (MK_COMB (@lem5992143 A C x op f g s) (@lem5992090 A C x op f g s)). Qed.
Lemma lem5992145 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5992146 {A C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : A -> C) (s : A -> Prop) : (term894 A C x op f g s) = (term895 A C x op f g s).
Proof. exact (MK_COMB (@lem5992145) (@lem5992144 A C x op f g s)). Qed.
Lemma lem5992147 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term896 A C x f op s g) = (term897 A C x f op s g).
Proof. exact (MK_COMB (@lem5992146 A C x op f g s) (@lem5992001 A C f op s g)). Qed.
Lemma lem5992148 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) (g : A -> C) : (term898 A C x f op g) = (term899 A C x f op g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5992147 A C x f op s g)). Qed.
Lemma lem5992149 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5992150 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) (g : A -> C) : (term900 A C x f op g) = (term901 A C x f op g).
Proof. exact (MK_COMB (@lem5992149 A) (@lem5992148 A C x f op g)). Qed.
Lemma lem5992151 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) : (term902 A C x f op) = (term903 A C x f op).
Proof. exact (fun_ext (fun g : A -> C => @lem5992150 A C x f op g)). Qed.
Lemma lem5992152 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem5992153 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) : (term904 A C x f op) = (term905 A C x f op).
Proof. exact (MK_COMB (@lem5992152 A C) (@lem5992151 A C x f op)). Qed.
Lemma lem5992154 {A C : Type'} (x : type747 A C) (op : type1400 C) : (term906 A C x op) = (term907 A C x op).
Proof. exact (fun_ext (fun f : A -> C => @lem5992153 A C x f op)). Qed.
Lemma lem5992155 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem5992156 {A C : Type'} (x : type747 A C) (op : type1400 C) : (term908 A C x op) = (term909 A C x op).
Proof. exact (MK_COMB (@lem5992155 A C) (@lem5992154 A C x op)). Qed.
Lemma lem5992157 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5992162 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5992163 {C : Type'} (f : type403 C) (x : type1400 C) : (f x) = (@I ((C -> C -> C) -> Prop) f x).
Proof. exact (@lem5992162 (type1400 C) Prop f x). Qed.
Lemma lem5992165 {C : Type'} (op : type1400 C) : (@monoidal C op) = (@I ((C -> C -> C) -> Prop) (@monoidal C) op).
Proof. exact (@lem5992163 C (@monoidal C) op). Qed.
Lemma lem5992166 {C : Type'} (op : type1400 C) : (term642 C op) = (term910 C op).
Proof. exact (MK_COMB (@lem5992157) (@lem5992165 C op)). Qed.
Lemma lem5992167 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5992168 {C : Type'} (op : type1400 C) : (term540 C op) = (term911 C op).
Proof. exact (MK_COMB (@lem5992167) (@lem5992166 C op)). Qed.
Lemma lem5992169 {A C : Type'} (x : type747 A C) (op : type1400 C) : (term670 A C x op) = (term912 A C x op).
Proof. exact (MK_COMB (@lem5992168 C op) (@lem5992156 A C x op)). Qed.
Lemma lem5992170 {A C : Type'} (x : type747 A C) : (term672 A C x) = (term913 A C x).
Proof. exact (fun_ext (fun op : type1400 C => @lem5992169 A C x op)). Qed.
Lemma lem5992171 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem5992172 {A C : Type'} (x : type747 A C) : (term674 A C x) = (term914 A C x).
Proof. exact (MK_COMB (@lem5992171 C) (@lem5992170 A C x)). Qed.
Lemma lem5992173 {A C : Type'} (x : type747 A C) (h1 : term674 A C x) : term914 A C x.
Proof. exact (EQ_MP (@lem5992172 A C x) (@lem5991674 A C x h1)). Qed.
Lemma lem5992813 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term845 A B C s t g h f x) = (term915 A B C t s g h f x).
Proof. exact (@lem19490 (term838 A B h x t) (term843 A x s) ((term830 A B C g h x) = (@I (A -> C) f x))). Qed.
Lemma lem5992814 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term846 A B C s t g h f) = (term916 A B C t s g h f).
Proof. exact (fun_ext (fun x : A => @lem5992813 A B C t s g h f x)). Qed.
Lemma lem5992815 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5992817 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term847 A B C s t g h f) = (term917 A B C t s g h f).
Proof. exact (MK_COMB (@lem5992815 A) (@lem5992814 A B C t s g h f)). Qed.
Lemma lem5992818 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term917 A B C t s g h f.
Proof. exact (EQ_MP (@lem5992817 A B C t s g h f) (@lem5991764 A B C s t g h f h1)). Qed.
Lemma lem5992837 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : ((term859 A B C f g x) = (term830 A B C f g x)) = ((term859 A B C f g x) = (term830 A B C f g x)).
Proof. exact (eq_refl ((term859 A B C f g x) = (term830 A B C f g x))). Qed.
Lemma lem5992838 {A B C : Type'} (f : B -> C) (g : A -> B) : (term862 A B C f g) = (term862 A B C f g).
Proof. exact (fun_ext (fun x : A => @lem5992837 A B C f g x)). Qed.
Lemma lem5992839 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5992840 {A B C : Type'} (f : B -> C) (g : A -> B) : (term863 A B C f g) = (term863 A B C f g).
Proof. exact (MK_COMB (@lem5992839 A) (@lem5992838 A B C f g)). Qed.
Lemma lem5992841 {A B C : Type'} (f : B -> C) : (term864 A B C f) = (term864 A B C f).
Proof. exact (fun_ext (fun g : A -> B => @lem5992840 A B C f g)). Qed.
Lemma lem5992842 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5992843 {A B C : Type'} (f : B -> C) : (term865 A B C f) = (term865 A B C f).
Proof. exact (MK_COMB (@lem5992842 A B) (@lem5992841 A B C f)). Qed.
Lemma lem5992844 {A B C : Type'} : (term866 A B C) = (term866 A B C).
Proof. exact (fun_ext (fun f : B -> C => @lem5992843 A B C f)). Qed.
Lemma lem5992845 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem5992847 {A B C : Type'} : (term867 A B C) = (term867 A B C).
Proof. exact (MK_COMB (@lem5992845 B C) (@lem5992844 A B C)). Qed.
Lemma lem5992848 {A B C : Type'} (h1 : term431 A B C) : term867 A B C.
Proof. exact (EQ_MP (@lem5992847 A B C) (@lem5991946 A B C h1)). Qed.
Lemma lem5992850 {A : Type'} (P : Prop) (Q : A -> Prop) : (term136 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5992851 {A C : Type'} (P : Prop) (Q : type572 A C) : (term918 A C P Q) = (term919 A C P Q).
Proof. exact (@lem5992850 (A -> C) P Q). Qed.
Lemma lem5992852 {A C : Type'} (x : type747 A C) (op : type1400 C) : (term920 A C x op) = (term921 A C x op).
Proof. exact (@lem5992851 A C (term910 C op) (term907 A C x op)). Qed.
Lemma lem5992853 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) : (term922 A C x op f) = (term905 A C x f op).
Proof. exact (eq_refl (term922 A C x op f)). Qed.
Lemma lem5992854 {A C : Type'} (x : type747 A C) (op : type1400 C) : (term923 A C x op) = (term907 A C x op).
Proof. exact (fun_ext (fun f : A -> C => @lem5992853 A C x f op)). Qed.
Lemma lem5992855 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem5992856 {A C : Type'} (x : type747 A C) (op : type1400 C) : (term924 A C x op) = (term909 A C x op).
Proof. exact (MK_COMB (@lem5992855 A C) (@lem5992854 A C x op)). Qed.
Lemma lem5992857 {C : Type'} (op : type1400 C) : (term911 C op) = (term911 C op).
Proof. exact (eq_refl (term911 C op)). Qed.
Lemma lem5992858 {A C : Type'} (x : type747 A C) (op : type1400 C) : (term920 A C x op) = (term912 A C x op).
Proof. exact (MK_COMB (@lem5992857 C op) (@lem5992856 A C x op)). Qed.
Lemma lem5992859 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5992860 {A C : Type'} (x : type747 A C) (op : type1400 C) : (term925 A C x op) = (term926 A C x op).
Proof. exact (MK_COMB (@lem5992859) (@lem5992858 A C x op)). Qed.
Lemma lem5992861 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) : (term922 A C x op f) = (term905 A C x f op).
Proof. exact (eq_refl (term922 A C x op f)). Qed.
Lemma lem5992862 {C : Type'} (op : type1400 C) : (term911 C op) = (term911 C op).
Proof. exact (eq_refl (term911 C op)). Qed.
Lemma lem5992863 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) : (term927 A C x op f) = (term928 A C x f op).
Proof. exact (MK_COMB (@lem5992862 C op) (@lem5992861 A C x f op)). Qed.
Lemma lem5992864 {A C : Type'} (x : type747 A C) (op : type1400 C) : (term929 A C x op) = (term930 A C x op).
Proof. exact (fun_ext (fun f : A -> C => @lem5992863 A C x f op)). Qed.
Lemma lem5992865 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem5992866 {A C : Type'} (x : type747 A C) (op : type1400 C) : (term921 A C x op) = (term931 A C x op).
Proof. exact (MK_COMB (@lem5992865 A C) (@lem5992864 A C x op)). Qed.
Lemma lem5992867 {A C : Type'} (x : type747 A C) (op : type1400 C) : ((term920 A C x op) = (term921 A C x op)) = ((term912 A C x op) = (term931 A C x op)).
Proof. exact (MK_COMB (@lem5992860 A C x op) (@lem5992866 A C x op)). Qed.
Lemma lem5992868 {A C : Type'} (x : type747 A C) (op : type1400 C) : (term912 A C x op) = (term931 A C x op).
Proof. exact (EQ_MP (@lem5992867 A C x op) (@lem5992852 A C x op)). Qed.
Lemma lem5992870 {A : Type'} (P : Prop) (Q : A -> Prop) : (term136 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5992871 {A C : Type'} (P : Prop) (Q : type572 A C) : (term918 A C P Q) = (term919 A C P Q).
Proof. exact (@lem5992870 (A -> C) P Q). Qed.
Lemma lem5992872 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) : (term932 A C x f op) = (term933 A C x f op).
Proof. exact (@lem5992871 A C (term910 C op) (term903 A C x f op)). Qed.
Lemma lem5992873 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) (g : A -> C) : (term934 A C x f op g) = (term901 A C x f op g).
Proof. exact (eq_refl (term934 A C x f op g)). Qed.
Lemma lem5992874 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) : (term935 A C x f op) = (term903 A C x f op).
Proof. exact (fun_ext (fun g : A -> C => @lem5992873 A C x f op g)). Qed.
Lemma lem5992875 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem5992876 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) : (term936 A C x f op) = (term905 A C x f op).
Proof. exact (MK_COMB (@lem5992875 A C) (@lem5992874 A C x f op)). Qed.
Lemma lem5992877 {C : Type'} (op : type1400 C) : (term911 C op) = (term911 C op).
Proof. exact (eq_refl (term911 C op)). Qed.
Lemma lem5992878 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) : (term932 A C x f op) = (term928 A C x f op).
Proof. exact (MK_COMB (@lem5992877 C op) (@lem5992876 A C x f op)). Qed.
Lemma lem5992879 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5992880 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) : (term937 A C x f op) = (term938 A C x f op).
Proof. exact (MK_COMB (@lem5992879) (@lem5992878 A C x f op)). Qed.
Lemma lem5992881 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) (g : A -> C) : (term934 A C x f op g) = (term901 A C x f op g).
Proof. exact (eq_refl (term934 A C x f op g)). Qed.
Lemma lem5992882 {C : Type'} (op : type1400 C) : (term911 C op) = (term911 C op).
Proof. exact (eq_refl (term911 C op)). Qed.
Lemma lem5992883 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) (g : A -> C) : (term939 A C x f op g) = (term940 A C x f op g).
Proof. exact (MK_COMB (@lem5992882 C op) (@lem5992881 A C x f op g)). Qed.
Lemma lem5992884 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) : (term941 A C x f op) = (term942 A C x f op).
Proof. exact (fun_ext (fun g : A -> C => @lem5992883 A C x f op g)). Qed.
Lemma lem5992885 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem5992886 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) : (term933 A C x f op) = (term943 A C x f op).
Proof. exact (MK_COMB (@lem5992885 A C) (@lem5992884 A C x f op)). Qed.
Lemma lem5992887 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) : ((term932 A C x f op) = (term933 A C x f op)) = ((term928 A C x f op) = (term943 A C x f op)).
Proof. exact (MK_COMB (@lem5992880 A C x f op) (@lem5992886 A C x f op)). Qed.
Lemma lem5992888 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) : (term928 A C x f op) = (term943 A C x f op).
Proof. exact (EQ_MP (@lem5992887 A C x f op) (@lem5992872 A C x f op)). Qed.
Lemma lem5992890 {A : Type'} (P : Prop) (Q : A -> Prop) : (term136 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5992891 {A : Type'} (P : Prop) (Q : type686 A) : (term944 A P Q) = (term945 A P Q).
Proof. exact (@lem5992890 (A -> Prop) P Q). Qed.
Lemma lem5992892 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) (g : A -> C) : (term946 A C x f op g) = (term947 A C x f op g).
Proof. exact (@lem5992891 A (term910 C op) (term899 A C x f op g)). Qed.
Lemma lem5992893 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term948 A C x f op g s) = (term897 A C x f op s g).
Proof. exact (eq_refl (term948 A C x f op g s)). Qed.
Lemma lem5992894 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) (g : A -> C) : (term949 A C x f op g) = (term899 A C x f op g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5992893 A C x f op s g)). Qed.
Lemma lem5992895 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5992896 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) (g : A -> C) : (term950 A C x f op g) = (term901 A C x f op g).
Proof. exact (MK_COMB (@lem5992895 A) (@lem5992894 A C x f op g)). Qed.
Lemma lem5992897 {C : Type'} (op : type1400 C) : (term911 C op) = (term911 C op).
Proof. exact (eq_refl (term911 C op)). Qed.
Lemma lem5992898 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) (g : A -> C) : (term946 A C x f op g) = (term940 A C x f op g).
Proof. exact (MK_COMB (@lem5992897 C op) (@lem5992896 A C x f op g)). Qed.
Lemma lem5992899 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5992900 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) (g : A -> C) : (term951 A C x f op g) = (term952 A C x f op g).
Proof. exact (MK_COMB (@lem5992899) (@lem5992898 A C x f op g)). Qed.
Lemma lem5992901 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term948 A C x f op g s) = (term897 A C x f op s g).
Proof. exact (eq_refl (term948 A C x f op g s)). Qed.
Lemma lem5992902 {C : Type'} (op : type1400 C) : (term911 C op) = (term911 C op).
Proof. exact (eq_refl (term911 C op)). Qed.
Lemma lem5992903 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term953 A C x f op g s) = (term954 A C x f op s g).
Proof. exact (MK_COMB (@lem5992902 C op) (@lem5992901 A C x f op s g)). Qed.
Lemma lem5992904 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) (g : A -> C) : (term955 A C x f op g) = (term956 A C x f op g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5992903 A C x f op s g)). Qed.
Lemma lem5992905 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5992906 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) (g : A -> C) : (term947 A C x f op g) = (term957 A C x f op g).
Proof. exact (MK_COMB (@lem5992905 A) (@lem5992904 A C x f op g)). Qed.
Lemma lem5992907 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) (g : A -> C) : ((term946 A C x f op g) = (term947 A C x f op g)) = ((term940 A C x f op g) = (term957 A C x f op g)).
Proof. exact (MK_COMB (@lem5992900 A C x f op g) (@lem5992906 A C x f op g)). Qed.
Lemma lem5992908 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) (g : A -> C) : (term940 A C x f op g) = (term957 A C x f op g).
Proof. exact (EQ_MP (@lem5992907 A C x f op g) (@lem5992892 A C x f op g)). Qed.
Lemma lem5992909 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) : (term942 A C x f op) = (term958 A C x f op).
Proof. exact (fun_ext (fun g : A -> C => @lem5992908 A C x f op g)). Qed.
Lemma lem5992910 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem5992911 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) : (term943 A C x f op) = (term959 A C x f op).
Proof. exact (MK_COMB (@lem5992910 A C) (@lem5992909 A C x f op)). Qed.
Lemma lem5992912 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) : (term928 A C x f op) = (term959 A C x f op).
Proof. exact (TRANS (@lem5992888 A C x f op) (@lem5992911 A C x f op)). Qed.
Lemma lem5992913 {A C : Type'} (x : type747 A C) (op : type1400 C) : (term930 A C x op) = (term960 A C x op).
Proof. exact (fun_ext (fun f : A -> C => @lem5992912 A C x f op)). Qed.
Lemma lem5992914 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem5992915 {A C : Type'} (x : type747 A C) (op : type1400 C) : (term931 A C x op) = (term961 A C x op).
Proof. exact (MK_COMB (@lem5992914 A C) (@lem5992913 A C x op)). Qed.
Lemma lem5992916 {A C : Type'} (x : type747 A C) (op : type1400 C) : (term912 A C x op) = (term961 A C x op).
Proof. exact (TRANS (@lem5992868 A C x op) (@lem5992915 A C x op)). Qed.
Lemma lem5992917 {A C : Type'} (x : type747 A C) : (term913 A C x) = (term962 A C x).
Proof. exact (fun_ext (fun op : type1400 C => @lem5992916 A C x op)). Qed.
Lemma lem5992918 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem5992919 {A C : Type'} (x : type747 A C) : (term914 A C x) = (term963 A C x).
Proof. exact (MK_COMB (@lem5992918 C) (@lem5992917 A C x)). Qed.
Lemma lem5992936 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term897 A C x f op s g) = (term964 A C x f op s g).
Proof. exact (@lem19699 (term889 A C x op f g s) (term882 A C x op f g s) ((term850 A C op s f) = (term850 A C op s g))). Qed.
Lemma lem5992939 {C : Type'} (op : type1400 C) : (term911 C op) = (term911 C op).
Proof. exact (eq_refl (term911 C op)). Qed.
Lemma lem5992940 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term954 A C x f op s g) = (term965 A C x f op s g).
Proof. exact (MK_COMB (@lem5992939 C op) (@lem5992936 A C x f op s g)). Qed.
Lemma lem5992947 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term965 A C x f op s g) = (term966 A C x f op s g).
Proof. exact (@lem19490 (term967 A C x f op s g) (term910 C op) (term968 A C x f op s g)). Qed.
Lemma lem5992948 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term954 A C x f op s g) = (term966 A C x f op s g).
Proof. exact (TRANS (@lem5992940 A C x f op s g) (@lem5992947 A C x f op s g)). Qed.
Lemma lem5992949 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) (g : A -> C) : (term956 A C x f op g) = (term969 A C x f op g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5992948 A C x f op s g)). Qed.
Lemma lem5992950 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5992951 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) (g : A -> C) : (term957 A C x f op g) = (term970 A C x f op g).
Proof. exact (MK_COMB (@lem5992950 A) (@lem5992949 A C x f op g)). Qed.
Lemma lem5992952 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) : (term958 A C x f op) = (term971 A C x f op).
Proof. exact (fun_ext (fun g : A -> C => @lem5992951 A C x f op g)). Qed.
Lemma lem5992953 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem5992954 {A C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) : (term959 A C x f op) = (term972 A C x f op).
Proof. exact (MK_COMB (@lem5992953 A C) (@lem5992952 A C x f op)). Qed.
Lemma lem5992955 {A C : Type'} (x : type747 A C) (op : type1400 C) : (term960 A C x op) = (term973 A C x op).
Proof. exact (fun_ext (fun f : A -> C => @lem5992954 A C x f op)). Qed.
Lemma lem5992956 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem5992957 {A C : Type'} (x : type747 A C) (op : type1400 C) : (term961 A C x op) = (term974 A C x op).
Proof. exact (MK_COMB (@lem5992956 A C) (@lem5992955 A C x op)). Qed.
Lemma lem5992958 {A C : Type'} (x : type747 A C) : (term962 A C x) = (term975 A C x).
Proof. exact (fun_ext (fun op : type1400 C => @lem5992957 A C x op)). Qed.
Lemma lem5992959 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem5992960 {A C : Type'} (x : type747 A C) : (term963 A C x) = (term976 A C x).
Proof. exact (MK_COMB (@lem5992959 C) (@lem5992958 A C x)). Qed.
Lemma lem5992961 {A C : Type'} (x : type747 A C) : (term914 A C x) = (term976 A C x).
Proof. exact (TRANS (@lem5992919 A C x) (@lem5992960 A C x)). Qed.
Lemma lem5992962 {A C : Type'} (x : type747 A C) (h1 : term674 A C x) : term976 A C x.
Proof. exact (EQ_MP (@lem5992961 A C x) (@lem5992173 A C x h1)). Qed.
Lemma lem5993373 {A B C : Type'} (_76109 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term977 A B C t s g h f _76109.
Proof. exact (@lem5992818 A B C s t g h f h1 _76109). Qed.
Lemma lem5993374 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (_76109 : A) : (term977 A B C t s g h f _76109) = (term915 A B C t s g h f _76109).
Proof. exact (eq_refl (term977 A B C t s g h f _76109)). Qed.
Lemma lem5993375 {A B C : Type'} (_76109 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term915 A B C t s g h f _76109.
Proof. exact (EQ_MP (@lem5993374 A B C t s g h f _76109) (@lem5993373 A B C _76109 s t g h f h1)). Qed.
Lemma lem5993385 {A B C : Type'} (_76113 : B -> C) (h1 : term431 A B C) : term978 A B C _76113.
Proof. exact (@lem5992848 A B C h1 _76113). Qed.
Lemma lem5993386 {A B C : Type'} (_76113 : B -> C) : (term978 A B C _76113) = (term865 A B C _76113).
Proof. exact (eq_refl (term978 A B C _76113)). Qed.
Lemma lem5993387 {A B C : Type'} (_76113 : B -> C) (h1 : term431 A B C) : term865 A B C _76113.
Proof. exact (EQ_MP (@lem5993386 A B C _76113) (@lem5993385 A B C _76113 h1)). Qed.
Lemma lem5993388 {A B C : Type'} (_76113 : B -> C) (_76114 : A -> B) (h1 : term431 A B C) : term979 A B C _76113 _76114.
Proof. exact (@lem5993387 A B C _76113 h1 _76114). Qed.
Lemma lem5993389 {A B C : Type'} (_76113 : B -> C) (_76114 : A -> B) : (term979 A B C _76113 _76114) = (term863 A B C _76113 _76114).
Proof. exact (eq_refl (term979 A B C _76113 _76114)). Qed.
Lemma lem5993390 {A B C : Type'} (_76113 : B -> C) (_76114 : A -> B) (h1 : term431 A B C) : term863 A B C _76113 _76114.
Proof. exact (EQ_MP (@lem5993389 A B C _76113 _76114) (@lem5993388 A B C _76113 _76114 h1)). Qed.
Lemma lem5993391 {A B C : Type'} (_76113 : B -> C) (_76114 : A -> B) (_76115 : A) (h1 : term431 A B C) : term980 A B C _76113 _76114 _76115.
Proof. exact (@lem5993390 A B C _76113 _76114 h1 _76115). Qed.
Lemma lem5993392 {A B C : Type'} (_76113 : B -> C) (_76114 : A -> B) (_76115 : A) : (term980 A B C _76113 _76114 _76115) = ((term859 A B C _76113 _76114 _76115) = (term830 A B C _76113 _76114 _76115)).
Proof. exact (eq_refl (term980 A B C _76113 _76114 _76115)). Qed.
Lemma lem5993394 {A C : Type'} (_76116 : type1400 C) (x : type747 A C) (h1 : term674 A C x) : term981 A C x _76116.
Proof. exact (@lem5992962 A C x h1 _76116). Qed.
Lemma lem5993395 {A C : Type'} (x : type747 A C) (_76116 : type1400 C) : (term981 A C x _76116) = (term974 A C x _76116).
Proof. exact (eq_refl (term981 A C x _76116)). Qed.
Lemma lem5993396 {A C : Type'} (_76116 : type1400 C) (x : type747 A C) (h1 : term674 A C x) : term974 A C x _76116.
Proof. exact (EQ_MP (@lem5993395 A C x _76116) (@lem5993394 A C _76116 x h1)). Qed.
Lemma lem5993397 {A C : Type'} (_76116 : type1400 C) (_76117 : A -> C) (x : type747 A C) (h1 : term674 A C x) : term982 A C x _76116 _76117.
Proof. exact (@lem5993396 A C _76116 x h1 _76117). Qed.
Lemma lem5993398 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76116 : type1400 C) : (term982 A C x _76116 _76117) = (term972 A C x _76117 _76116).
Proof. exact (eq_refl (term982 A C x _76116 _76117)). Qed.
Lemma lem5993399 {A C : Type'} (_76117 : A -> C) (_76116 : type1400 C) (x : type747 A C) (h1 : term674 A C x) : term972 A C x _76117 _76116.
Proof. exact (EQ_MP (@lem5993398 A C x _76117 _76116) (@lem5993397 A C _76116 _76117 x h1)). Qed.
Lemma lem5993400 {A C : Type'} (_76117 : A -> C) (_76116 : type1400 C) (_76118 : A -> C) (x : type747 A C) (h1 : term674 A C x) : term983 A C x _76117 _76116 _76118.
Proof. exact (@lem5993399 A C _76117 _76116 x h1 _76118). Qed.
Lemma lem5993401 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76116 : type1400 C) (_76118 : A -> C) : (term983 A C x _76117 _76116 _76118) = (term970 A C x _76117 _76116 _76118).
Proof. exact (eq_refl (term983 A C x _76117 _76116 _76118)). Qed.
Lemma lem5993402 {A C : Type'} (_76117 : A -> C) (_76116 : type1400 C) (_76118 : A -> C) (x : type747 A C) (h1 : term674 A C x) : term970 A C x _76117 _76116 _76118.
Proof. exact (EQ_MP (@lem5993401 A C x _76117 _76116 _76118) (@lem5993400 A C _76117 _76116 _76118 x h1)). Qed.
Lemma lem5993403 {A C : Type'} (_76117 : A -> C) (_76116 : type1400 C) (_76118 : A -> C) (_76119 : A -> Prop) (x : type747 A C) (h1 : term674 A C x) : term984 A C x _76117 _76116 _76118 _76119.
Proof. exact (@lem5993402 A C _76117 _76116 _76118 x h1 _76119). Qed.
Lemma lem5993404 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76116 : type1400 C) (_76119 : A -> Prop) (_76118 : A -> C) : (term984 A C x _76117 _76116 _76118 _76119) = (term966 A C x _76117 _76116 _76119 _76118).
Proof. exact (eq_refl (term984 A C x _76117 _76116 _76118 _76119)). Qed.
Lemma lem5993405 {A C : Type'} (_76117 : A -> C) (_76116 : type1400 C) (_76119 : A -> Prop) (_76118 : A -> C) (x : type747 A C) (h1 : term674 A C x) : term966 A C x _76117 _76116 _76119 _76118.
Proof. exact (EQ_MP (@lem5993404 A C x _76117 _76116 _76119 _76118) (@lem5993403 A C _76117 _76116 _76118 _76119 x h1)). Qed.
Lemma lem5993454 {A B C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term427 A B C f op s g h) : term857 A B C f op s g h.
Proof. exact (EQ_MP (@lem5991837 A B C f op s g h) (@lem5990479 A B C f op s g h h1)). Qed.
Lemma lem5993546 {A C : Type'} (_76117 : A -> C) (_76116 : type1400 C) (_76119 : A -> Prop) (_76118 : A -> C) (x : type747 A C) (h1 : term674 A C x) : term985 A C x _76117 _76116 _76119 _76118.
Proof. exact (proj1 (@lem5993405 A C _76117 _76116 _76119 _76118 x h1)). Qed.
Lemma lem5993556 {A C : Type'} (_76117 : A -> C) (_76116 : type1400 C) (_76119 : A -> Prop) (_76118 : A -> C) (x : type747 A C) (h1 : term674 A C x) : term986 A C x _76117 _76116 _76119 _76118.
Proof. exact (proj2 (@lem5993405 A C _76117 _76116 _76119 _76118 x h1)). Qed.
Lemma lem5993568 {A B C : Type'} (_76109 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term987 A B C s g h f _76109.
Proof. exact (proj2 (@lem5993375 A B C _76109 s t g h f h1)). Qed.
Lemma lem5994111 {C : Type'} (x : C) (y : C) (z : C) : term358 C x y z.
Proof. exact (@lem21385 C x y z). Qed.
Lemma lem5994195 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @I ((C -> C -> C) -> Prop) (@monoidal C) op.
Proof. exact (EQ_MP (@lem5991685 C op) (@lem5989994 C op h1)). Qed.
Lemma lem5994196 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term988 C op.
Proof. exact (fun h0 : term910 C op => @lem5994195 C op h1). Qed.
Lemma lem5994198 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5994199 {C : Type'} (op : type1400 C) : (term988 C op) = (@I ((C -> C -> C) -> Prop) (@monoidal C) op).
Proof. exact (@lem5994198 (@I ((C -> C -> C) -> Prop) (@monoidal C) op)). Qed.
Lemma lem5994200 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @I ((C -> C -> C) -> Prop) (@monoidal C) op.
Proof. exact (EQ_MP (@lem5994199 C op) (@lem5994196 C op h1)). Qed.
Lemma lem5994202 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @I ((C -> C -> C) -> Prop) (@monoidal C) op.
Proof. exact (EQ_MP (@lem5991685 C op) (@lem5989994 C op h1)). Qed.
Lemma lem5994203 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term988 C op.
Proof. exact (fun h0 : term910 C op => @lem5994202 C op h1). Qed.
Lemma lem5994205 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5994206 {C : Type'} (op : type1400 C) : (term988 C op) = (@I ((C -> C -> C) -> Prop) (@monoidal C) op).
Proof. exact (@lem5994205 (@I ((C -> C -> C) -> Prop) (@monoidal C) op)). Qed.
Lemma lem5994207 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @I ((C -> C -> C) -> Prop) (@monoidal C) op.
Proof. exact (EQ_MP (@lem5994206 C op) (@lem5994203 C op h1)). Qed.
Lemma lem5994210 {A B C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term857 A B C f op s g h) : term857 A B C f op s g h.
Proof. exact (h1). Qed.
Lemma lem5994211 {A B C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term857 A B C f op s g h) : term989 A B C f op s g h.
Proof. exact (fun h0 : (term850 A C op s f) = (term854 A B C op s g h) => @lem5994210 A B C f op s g h h1). Qed.
Lemma lem5994213 (p : Prop) : (term990 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5994214 {A B C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term989 A B C f op s g h) = (term857 A B C f op s g h).
Proof. exact (@lem5994213 ((term850 A C op s f) = (term854 A B C op s g h))). Qed.
Lemma lem5994215 {A B C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term857 A B C f op s g h) : term857 A B C f op s g h.
Proof. exact (EQ_MP (@lem5994214 A B C f op s g h) (@lem5994211 A B C f op s g h h1)). Qed.
Lemma lem5994221 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5994222 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76116 : type1400 C) (_76119 : A -> Prop) (_76118 : A -> C) : (term985 A C x _76117 _76116 _76119 _76118) = (term991 A C x _76117 _76116 _76119 _76118).
Proof. exact (@lem5994221 (term889 A C x _76116 _76117 _76118 _76119) (term910 C _76116) ((term850 A C _76116 _76119 _76117) = (term850 A C _76116 _76119 _76118))). Qed.
Lemma lem5994236 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5994237 {A C : Type'} (_76117 : A -> C) (_76119 : A -> Prop) (_76118 : A -> C) (_76116 : type1400 C) : (term992 A C _76117 _76116 _76119 _76118) = (term993 A C _76117 _76119 _76118 _76116).
Proof. exact (@lem5994236 ((term850 A C _76116 _76119 _76117) = (term850 A C _76116 _76119 _76118)) (term910 C _76116)). Qed.
Lemma lem5994245 {A C : Type'} (x : type747 A C) (_76116 : type1400 C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) : (term994 A C x _76116 _76117 _76118 _76119) = (term994 A C x _76116 _76117 _76118 _76119).
Proof. exact (eq_refl (term994 A C x _76116 _76117 _76118 _76119)). Qed.
Lemma lem5994246 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76119 : A -> Prop) (_76118 : A -> C) (_76116 : type1400 C) : (term991 A C x _76117 _76116 _76119 _76118) = (term995 A C x _76117 _76119 _76118 _76116).
Proof. exact (MK_COMB (@lem5994245 A C x _76116 _76117 _76118 _76119) (@lem5994237 A C _76117 _76119 _76118 _76116)). Qed.
Lemma lem5994250 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5994251 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) (_76116 : type1400 C) : (term995 A C x _76117 _76119 _76118 _76116) = (term996 A C x _76117 _76118 _76119 _76116).
Proof. exact (@lem5994250 ((term850 A C _76116 _76119 _76117) = (term850 A C _76116 _76119 _76118)) (term889 A C x _76116 _76117 _76118 _76119) (term910 C _76116)). Qed.
Lemma lem5994269 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) (_76116 : type1400 C) : (term991 A C x _76117 _76116 _76119 _76118) = (term996 A C x _76117 _76118 _76119 _76116).
Proof. exact (TRANS (@lem5994246 A C x _76117 _76119 _76118 _76116) (@lem5994251 A C x _76117 _76118 _76119 _76116)). Qed.
Lemma lem5994270 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) (_76116 : type1400 C) : (term985 A C x _76117 _76116 _76119 _76118) = (term996 A C x _76117 _76118 _76119 _76116).
Proof. exact (TRANS (@lem5994222 A C x _76117 _76116 _76119 _76118) (@lem5994269 A C x _76117 _76118 _76119 _76116)). Qed.
Lemma lem5994271 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5994272 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) (_76116 : type1400 C) : (term997 A C x _76117 _76116 _76119 _76118) = (term998 A C x _76117 _76118 _76119 _76116).
Proof. exact (MK_COMB (@lem5994271) (@lem5994270 A C x _76117 _76118 _76119 _76116)). Qed.
Lemma lem5994286 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5994287 {A C : Type'} (_76117 : A -> C) (_76119 : A -> Prop) (_76118 : A -> C) (_76116 : type1400 C) : (term992 A C _76117 _76116 _76119 _76118) = (term993 A C _76117 _76119 _76118 _76116).
Proof. exact (@lem5994286 ((term850 A C _76116 _76119 _76117) = (term850 A C _76116 _76119 _76118)) (term910 C _76116)). Qed.
Lemma lem5994295 {A C : Type'} (x : type747 A C) (_76116 : type1400 C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) : (term994 A C x _76116 _76117 _76118 _76119) = (term994 A C x _76116 _76117 _76118 _76119).
Proof. exact (eq_refl (term994 A C x _76116 _76117 _76118 _76119)). Qed.
Lemma lem5994296 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76119 : A -> Prop) (_76118 : A -> C) (_76116 : type1400 C) : (term991 A C x _76117 _76116 _76119 _76118) = (term995 A C x _76117 _76119 _76118 _76116).
Proof. exact (MK_COMB (@lem5994295 A C x _76116 _76117 _76118 _76119) (@lem5994287 A C _76117 _76119 _76118 _76116)). Qed.
Lemma lem5994300 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5994301 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) (_76116 : type1400 C) : (term995 A C x _76117 _76119 _76118 _76116) = (term996 A C x _76117 _76118 _76119 _76116).
Proof. exact (@lem5994300 ((term850 A C _76116 _76119 _76117) = (term850 A C _76116 _76119 _76118)) (term889 A C x _76116 _76117 _76118 _76119) (term910 C _76116)). Qed.
Lemma lem5994319 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) (_76116 : type1400 C) : (term991 A C x _76117 _76116 _76119 _76118) = (term996 A C x _76117 _76118 _76119 _76116).
Proof. exact (TRANS (@lem5994296 A C x _76117 _76119 _76118 _76116) (@lem5994301 A C x _76117 _76118 _76119 _76116)). Qed.
Lemma lem5994320 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) (_76116 : type1400 C) : ((term985 A C x _76117 _76116 _76119 _76118) = (term991 A C x _76117 _76116 _76119 _76118)) = ((term996 A C x _76117 _76118 _76119 _76116) = (term996 A C x _76117 _76118 _76119 _76116)).
Proof. exact (MK_COMB (@lem5994272 A C x _76117 _76118 _76119 _76116) (@lem5994319 A C x _76117 _76118 _76119 _76116)). Qed.
Lemma lem5994322 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5994323 (x : Prop) : (x = x) = True.
Proof. exact (@lem5994322 Prop x). Qed.
Lemma lem5994324 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) (_76116 : type1400 C) : ((term996 A C x _76117 _76118 _76119 _76116) = (term996 A C x _76117 _76118 _76119 _76116)) = True.
Proof. exact (@lem5994323 (term996 A C x _76117 _76118 _76119 _76116)). Qed.
Lemma lem5994325 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76116 : type1400 C) (_76119 : A -> Prop) (_76118 : A -> C) : ((term985 A C x _76117 _76116 _76119 _76118) = (term991 A C x _76117 _76116 _76119 _76118)) = True.
Proof. exact (TRANS (@lem5994320 A C x _76117 _76118 _76119 _76116) (@lem5994324 A C x _76117 _76118 _76119 _76116)). Qed.
Lemma lem5994326 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76116 : type1400 C) (_76119 : A -> Prop) (_76118 : A -> C) : True = ((term985 A C x _76117 _76116 _76119 _76118) = (term991 A C x _76117 _76116 _76119 _76118)).
Proof. exact (SYM (@lem5994325 A C x _76117 _76116 _76119 _76118)). Qed.
Lemma lem5994327 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76116 : type1400 C) (_76119 : A -> Prop) (_76118 : A -> C) : (term985 A C x _76117 _76116 _76119 _76118) = (term991 A C x _76117 _76116 _76119 _76118).
Proof. exact (EQ_MP (@lem5994326 A C x _76117 _76116 _76119 _76118) (@lem0)). Qed.
Lemma lem5994328 {A C : Type'} (_76117 : A -> C) (_76116 : type1400 C) (_76119 : A -> Prop) (_76118 : A -> C) (x : type747 A C) (h1 : term674 A C x) : term991 A C x _76117 _76116 _76119 _76118.
Proof. exact (EQ_MP (@lem5994327 A C x _76117 _76116 _76119 _76118) (@lem5993546 A C _76117 _76116 _76119 _76118 x h1)). Qed.
Lemma lem5994330 (b : Prop) (a : Prop) : (a \/ b) = (term364 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5994331 {A C : Type'} (x : type747 A C) (_76116 : type1400 C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) : (term991 A C x _76117 _76116 _76119 _76118) = (term999 A C x _76116 _76117 _76118 _76119).
Proof. exact (@lem5994330 (term992 A C _76117 _76116 _76119 _76118) (term889 A C x _76116 _76117 _76118 _76119)). Qed.
Lemma lem5994333 (a : Prop) (b : Prop) : (term383 a b) = (term384 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5994334 {A C : Type'} (_76117 : A -> C) (_76116 : type1400 C) (_76119 : A -> Prop) (_76118 : A -> C) : (term1000 A C _76117 _76116 _76119 _76118) = (term1001 A C _76117 _76116 _76119 _76118).
Proof. exact (@lem5994333 (term910 C _76116) ((term850 A C _76116 _76119 _76117) = (term850 A C _76116 _76119 _76118))). Qed.
Lemma lem5994336 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5994337 {C : Type'} (_76116 : type1400 C) : (term1002 C _76116) = (@I ((C -> C -> C) -> Prop) (@monoidal C) _76116).
Proof. exact (@lem5994336 (@I ((C -> C -> C) -> Prop) (@monoidal C) _76116)). Qed.
Lemma lem5994338 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5994339 {C : Type'} (_76116 : type1400 C) : (term1003 C _76116) = (term1004 C _76116).
Proof. exact (MK_COMB (@lem5994338) (@lem5994337 C _76116)). Qed.
Lemma lem5994340 {A C : Type'} (_76117 : A -> C) (_76116 : type1400 C) (_76119 : A -> Prop) (_76118 : A -> C) : (term1005 A C _76117 _76116 _76119 _76118) = (term1005 A C _76117 _76116 _76119 _76118).
Proof. exact (eq_refl (term1005 A C _76117 _76116 _76119 _76118)). Qed.
Lemma lem5994341 {A C : Type'} (_76117 : A -> C) (_76116 : type1400 C) (_76119 : A -> Prop) (_76118 : A -> C) : (term1001 A C _76117 _76116 _76119 _76118) = (term1006 A C _76117 _76116 _76119 _76118).
Proof. exact (MK_COMB (@lem5994339 C _76116) (@lem5994340 A C _76117 _76116 _76119 _76118)). Qed.
Lemma lem5994342 {A C : Type'} (_76117 : A -> C) (_76116 : type1400 C) (_76119 : A -> Prop) (_76118 : A -> C) : (term1000 A C _76117 _76116 _76119 _76118) = (term1006 A C _76117 _76116 _76119 _76118).
Proof. exact (TRANS (@lem5994334 A C _76117 _76116 _76119 _76118) (@lem5994341 A C _76117 _76116 _76119 _76118)). Qed.
Lemma lem5994343 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5994344 {A C : Type'} (_76117 : A -> C) (_76116 : type1400 C) (_76119 : A -> Prop) (_76118 : A -> C) : (term1007 A C _76117 _76116 _76119 _76118) = (term1008 A C _76117 _76116 _76119 _76118).
Proof. exact (MK_COMB (@lem5994343) (@lem5994342 A C _76117 _76116 _76119 _76118)). Qed.
Lemma lem5994345 {A C : Type'} (x : type747 A C) (_76116 : type1400 C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) : (term889 A C x _76116 _76117 _76118 _76119) = (term889 A C x _76116 _76117 _76118 _76119).
Proof. exact (eq_refl (term889 A C x _76116 _76117 _76118 _76119)). Qed.
Lemma lem5994346 {A C : Type'} (x : type747 A C) (_76116 : type1400 C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) : (term999 A C x _76116 _76117 _76118 _76119) = (term1009 A C x _76116 _76117 _76118 _76119).
Proof. exact (MK_COMB (@lem5994344 A C _76117 _76116 _76119 _76118) (@lem5994345 A C x _76116 _76117 _76118 _76119)). Qed.
Lemma lem5994347 {A C : Type'} (x : type747 A C) (_76116 : type1400 C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) : (term991 A C x _76117 _76116 _76119 _76118) = (term1009 A C x _76116 _76117 _76118 _76119).
Proof. exact (TRANS (@lem5994331 A C x _76116 _76117 _76118 _76119) (@lem5994346 A C x _76116 _76117 _76118 _76119)). Qed.
Lemma lem5994349 {A B C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : @monoidal C op) (h2 : term857 A B C f op s g h) : term1010 A B C f op s g h.
Proof. exact (conj (@lem5994207 C op h1) (@lem5994215 A B C f op s g h h2)). Qed.
Lemma lem5994351 {A C : Type'} (_76116 : type1400 C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) (x : type747 A C) (h1 : term674 A C x) : term1009 A C x _76116 _76117 _76118 _76119.
Proof. exact (EQ_MP (@lem5994347 A C x _76116 _76117 _76118 _76119) (@lem5994328 A C _76117 _76116 _76119 _76118 x h1)). Qed.
Lemma lem5994352 {A C : Type'} (_76116 : type1400 C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) (x : type747 A C) (h1 : term674 A C x) : term1009 A C x _76116 _76117 _76118 _76119.
Proof. exact (@lem5994351 A C _76116 _76117 _76118 _76119 x h1). Qed.
Lemma lem5994353 {A B C : Type'} (op : type1400 C) (f : A -> C) (g : B -> C) (h : A -> B) (s : A -> Prop) (x : type747 A C) (h1 : term674 A C x) : term1011 A B C x op f g h s.
Proof. exact (@lem5994352 A C op f (term851 A B C g h) s x h1). Qed.
Lemma lem5994356 {A B C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term674 A C x) (h2 : @monoidal C op) (h3 : term857 A B C f op s g h) : term1012 A B C x op f g h s.
Proof. exact (@lem5994353 A B C op f g h s x h1 (@lem5994349 A B C f op s g h h2 h3)). Qed.
Lemma lem5994357 {A B C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term674 A C x) (h2 : @monoidal C op) (h3 : term857 A B C f op s g h) : term1013 A B C x op f g h s.
Proof. exact (fun h0 : term1014 A B C x op f g h s => @lem5994356 A B C x f op s g h h1 h2 h3). Qed.
Lemma lem5994359 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5994360 {A B C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : B -> C) (h : A -> B) (s : A -> Prop) : (term1013 A B C x op f g h s) = (term1012 A B C x op f g h s).
Proof. exact (@lem5994359 (term1012 A B C x op f g h s)). Qed.
Lemma lem5994361 {A B C : Type'} (x : type747 A C) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term674 A C x) (h2 : @monoidal C op) (h3 : term857 A B C f op s g h) : term1012 A B C x op f g h s.
Proof. exact (EQ_MP (@lem5994360 A B C x op f g h s) (@lem5994357 A B C x f op s g h h1 h2 h3)). Qed.
Lemma lem5994367 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5994368 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) (_76109 : A) (s : A -> Prop) : (term987 A B C s g h f _76109) = (term1015 A B C g h f _76109 s).
Proof. exact (@lem5994367 ((term830 A B C g h _76109) = (@I (A -> C) f _76109)) (term843 A _76109 s)). Qed.
Lemma lem5994376 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5994377 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) (_76109 : A) (s : A -> Prop) : (term1016 A B C s g h f _76109) = (term1017 A B C g h f _76109 s).
Proof. exact (MK_COMB (@lem5994376) (@lem5994368 A B C g h f _76109 s)). Qed.
Lemma lem5994385 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) (_76109 : A) (s : A -> Prop) : (term1015 A B C g h f _76109 s) = (term1015 A B C g h f _76109 s).
Proof. exact (eq_refl (term1015 A B C g h f _76109 s)). Qed.
Lemma lem5994386 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) (_76109 : A) (s : A -> Prop) : ((term987 A B C s g h f _76109) = (term1015 A B C g h f _76109 s)) = ((term1015 A B C g h f _76109 s) = (term1015 A B C g h f _76109 s)).
Proof. exact (MK_COMB (@lem5994377 A B C g h f _76109 s) (@lem5994385 A B C g h f _76109 s)). Qed.
Lemma lem5994388 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5994389 (x : Prop) : (x = x) = True.
Proof. exact (@lem5994388 Prop x). Qed.
Lemma lem5994390 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) (_76109 : A) (s : A -> Prop) : ((term1015 A B C g h f _76109 s) = (term1015 A B C g h f _76109 s)) = True.
Proof. exact (@lem5994389 (term1015 A B C g h f _76109 s)). Qed.
Lemma lem5994391 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) (_76109 : A) (s : A -> Prop) : ((term987 A B C s g h f _76109) = (term1015 A B C g h f _76109 s)) = True.
Proof. exact (TRANS (@lem5994386 A B C g h f _76109 s) (@lem5994390 A B C g h f _76109 s)). Qed.
Lemma lem5994392 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) (_76109 : A) (s : A -> Prop) : True = ((term987 A B C s g h f _76109) = (term1015 A B C g h f _76109 s)).
Proof. exact (SYM (@lem5994391 A B C g h f _76109 s)). Qed.
Lemma lem5994393 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) (_76109 : A) (s : A -> Prop) : (term987 A B C s g h f _76109) = (term1015 A B C g h f _76109 s).
Proof. exact (EQ_MP (@lem5994392 A B C g h f _76109 s) (@lem0)). Qed.
Lemma lem5994394 {A B C : Type'} (_76109 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term1015 A B C g h f _76109 s.
Proof. exact (EQ_MP (@lem5994393 A B C g h f _76109 s) (@lem5993568 A B C _76109 s t g h f h1)). Qed.
Lemma lem5994396 (b : Prop) (a : Prop) : (a \/ b) = (term364 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5994397 {A B C : Type'} (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (_76109 : A) : (term1015 A B C g h f _76109 s) = (term1018 A B C s g h f _76109).
Proof. exact (@lem5994396 (term843 A _76109 s) ((term830 A B C g h _76109) = (@I (A -> C) f _76109))). Qed.
Lemma lem5994399 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5994400 {A : Type'} (_76109 : A) (s : A -> Prop) : (term1019 A _76109 s) = (term842 A _76109 s).
Proof. exact (@lem5994399 (term842 A _76109 s)). Qed.
Lemma lem5994401 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5994402 {A : Type'} (_76109 : A) (s : A -> Prop) : (term1020 A _76109 s) = (term1021 A _76109 s).
Proof. exact (MK_COMB (@lem5994401) (@lem5994400 A _76109 s)). Qed.
Lemma lem5994403 {A B C : Type'} (g : B -> C) (h : A -> B) (f : A -> C) (_76109 : A) : ((term830 A B C g h _76109) = (@I (A -> C) f _76109)) = ((term830 A B C g h _76109) = (@I (A -> C) f _76109)).
Proof. exact (eq_refl ((term830 A B C g h _76109) = (@I (A -> C) f _76109))). Qed.
Lemma lem5994404 {A B C : Type'} (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (_76109 : A) : (term1018 A B C s g h f _76109) = (term1022 A B C s g h f _76109).
Proof. exact (MK_COMB (@lem5994402 A _76109 s) (@lem5994403 A B C g h f _76109)). Qed.
Lemma lem5994405 {A B C : Type'} (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (_76109 : A) : (term1015 A B C g h f _76109 s) = (term1022 A B C s g h f _76109).
Proof. exact (TRANS (@lem5994397 A B C s g h f _76109) (@lem5994404 A B C s g h f _76109)). Qed.
Lemma lem5994408 {A B C : Type'} (_76109 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term1022 A B C s g h f _76109.
Proof. exact (EQ_MP (@lem5994405 A B C s g h f _76109) (@lem5994394 A B C _76109 s t g h f h1)). Qed.
Lemma lem5994409 {A B C : Type'} (_76109 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term1022 A B C s g h f _76109.
Proof. exact (@lem5994408 A B C _76109 s t g h f h1). Qed.
Lemma lem5994410 {A B C : Type'} (x : type747 A C) (op : type1400 C) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term1023 A B C x op f g h s.
Proof. exact (@lem5994409 A B C (term1024 A B C x op f g h s) s t g h f h1). Qed.
Lemma lem5994413 {A B C : Type'} (t : B -> Prop) (x : type747 A C) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term674 A C x) (h3 : @monoidal C op) (h4 : term857 A B C f op s g h) : (term1025 A B C x op f g h s) = (term1026 A B C x op f g h s).
Proof. exact (@lem5994410 A B C x op s t g h f h1 (@lem5994361 A B C x f op s g h h2 h3 h4)). Qed.
Lemma lem5994414 {A B C : Type'} (t : B -> Prop) (x : type747 A C) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term674 A C x) (h3 : @monoidal C op) (h4 : term857 A B C f op s g h) : term1027 A B C x op f g h s.
Proof. exact (fun h0 : term1028 A B C x op f g h s => @lem5994413 A B C t x f op s g h h1 h2 h3 h4). Qed.
Lemma lem5994416 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5994417 {A B C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : B -> C) (h : A -> B) (s : A -> Prop) : (term1027 A B C x op f g h s) = ((term1025 A B C x op f g h s) = (term1026 A B C x op f g h s)).
Proof. exact (@lem5994416 ((term1025 A B C x op f g h s) = (term1026 A B C x op f g h s))). Qed.
Lemma lem5994418 {A B C : Type'} (t : B -> Prop) (x : type747 A C) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term674 A C x) (h3 : @monoidal C op) (h4 : term857 A B C f op s g h) : (term1025 A B C x op f g h s) = (term1026 A B C x op f g h s).
Proof. exact (EQ_MP (@lem5994417 A B C x op f g h s) (@lem5994414 A B C t x f op s g h h1 h2 h3 h4)). Qed.
Lemma lem5994420 {A B C : Type'} (_76113 : B -> C) (_76114 : A -> B) (_76115 : A) (h1 : term431 A B C) : (term859 A B C _76113 _76114 _76115) = (term830 A B C _76113 _76114 _76115).
Proof. exact (EQ_MP (@lem5993392 A B C _76113 _76114 _76115) (@lem5993391 A B C _76113 _76114 _76115 h1)). Qed.
Lemma lem5994421 {A B C : Type'} (_76113 : B -> C) (_76114 : A -> B) (_76115 : A) (h1 : term431 A B C) : (term859 A B C _76113 _76114 _76115) = (term830 A B C _76113 _76114 _76115).
Proof. exact (@lem5994420 A B C _76113 _76114 _76115 h1). Qed.
Lemma lem5994422 {A B C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : B -> C) (h : A -> B) (s : A -> Prop) (h1 : term431 A B C) : (term1029 A B C x op f g h s) = (term1025 A B C x op f g h s).
Proof. exact (@lem5994421 A B C g h (term1024 A B C x op f g h s) h1). Qed.
Lemma lem5994423 {A B C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : B -> C) (h : A -> B) (s : A -> Prop) (h1 : term431 A B C) : term1030 A B C x op f g h s.
Proof. exact (fun h0 : term1031 A B C x op f g h s => @lem5994422 A B C x op f g h s h1). Qed.
Lemma lem5994425 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5994426 {A B C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : B -> C) (h : A -> B) (s : A -> Prop) : (term1030 A B C x op f g h s) = ((term1029 A B C x op f g h s) = (term1025 A B C x op f g h s)).
Proof. exact (@lem5994425 ((term1029 A B C x op f g h s) = (term1025 A B C x op f g h s))). Qed.
Lemma lem5994427 {A B C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : B -> C) (h : A -> B) (s : A -> Prop) (h1 : term431 A B C) : (term1029 A B C x op f g h s) = (term1025 A B C x op f g h s).
Proof. exact (EQ_MP (@lem5994426 A B C x op f g h s) (@lem5994423 A B C x op f g h s h1)). Qed.
Lemma lem5994429 {C : Type'} (x : C) : x = x.
Proof. exact (@lem21386 C x). Qed.
Lemma lem5994430 {C : Type'} (x : C) : x = x.
Proof. exact (@lem5994429 C x). Qed.
Lemma lem5994431 {A B C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : B -> C) (h : A -> B) (s : A -> Prop) : (term1029 A B C x op f g h s) = (term1029 A B C x op f g h s).
Proof. exact (@lem5994430 C (term1029 A B C x op f g h s)). Qed.
Lemma lem5994432 {A B C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : B -> C) (h : A -> B) (s : A -> Prop) : term1032 A B C x op f g h s.
Proof. exact (fun h0 : term1033 A B C x op f g h s => @lem5994431 A B C x op f g h s). Qed.
Lemma lem5994434 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5994435 {A B C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : B -> C) (h : A -> B) (s : A -> Prop) : (term1032 A B C x op f g h s) = ((term1029 A B C x op f g h s) = (term1029 A B C x op f g h s)).
Proof. exact (@lem5994434 ((term1029 A B C x op f g h s) = (term1029 A B C x op f g h s))). Qed.
Lemma lem5994436 {A B C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : B -> C) (h : A -> B) (s : A -> Prop) : (term1029 A B C x op f g h s) = (term1029 A B C x op f g h s).
Proof. exact (EQ_MP (@lem5994435 A B C x op f g h s) (@lem5994432 A B C x op f g h s)). Qed.
Lemma lem5994454 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5994455 {C : Type'} (y : C) (x : C) (z : C) : (term373 C x y z) = (term374 C y x z).
Proof. exact (@lem5994454 (y = z) (term375 C x z)). Qed.
Lemma lem5994465 {C : Type'} (x : C) (y : C) : (term376 C x y) = (term376 C x y).
Proof. exact (eq_refl (term376 C x y)). Qed.
Lemma lem5994466 {C : Type'} (y : C) (x : C) (z : C) : (term358 C x y z) = (term377 C y x z).
Proof. exact (MK_COMB (@lem5994465 C x y) (@lem5994455 C y x z)). Qed.
Lemma lem5994470 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5994471 {C : Type'} (y : C) (x : C) (z : C) : (term377 C y x z) = (term378 C y x z).
Proof. exact (@lem5994470 (y = z) (term375 C x y) (term375 C x z)). Qed.
Lemma lem5994493 {C : Type'} (y : C) (x : C) (z : C) : (term358 C x y z) = (term378 C y x z).
Proof. exact (TRANS (@lem5994466 C y x z) (@lem5994471 C y x z)). Qed.
Lemma lem5994494 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5994495 {C : Type'} (y : C) (x : C) (z : C) : (term379 C x y z) = (term380 C y x z).
Proof. exact (MK_COMB (@lem5994494) (@lem5994493 C y x z)). Qed.
Lemma lem5994517 {C : Type'} (y : C) (x : C) (z : C) : (term378 C y x z) = (term378 C y x z).
Proof. exact (eq_refl (term378 C y x z)). Qed.
Lemma lem5994518 {C : Type'} (y : C) (x : C) (z : C) : ((term358 C x y z) = (term378 C y x z)) = ((term378 C y x z) = (term378 C y x z)).
Proof. exact (MK_COMB (@lem5994495 C y x z) (@lem5994517 C y x z)). Qed.
Lemma lem5994520 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5994521 (x : Prop) : (x = x) = True.
Proof. exact (@lem5994520 Prop x). Qed.
Lemma lem5994522 {C : Type'} (y : C) (x : C) (z : C) : ((term378 C y x z) = (term378 C y x z)) = True.
Proof. exact (@lem5994521 (term378 C y x z)). Qed.
Lemma lem5994523 {C : Type'} (y : C) (x : C) (z : C) : ((term358 C x y z) = (term378 C y x z)) = True.
Proof. exact (TRANS (@lem5994518 C y x z) (@lem5994522 C y x z)). Qed.
Lemma lem5994524 {C : Type'} (y : C) (x : C) (z : C) : True = ((term358 C x y z) = (term378 C y x z)).
Proof. exact (SYM (@lem5994523 C y x z)). Qed.
Lemma lem5994525 {C : Type'} (y : C) (x : C) (z : C) : (term358 C x y z) = (term378 C y x z).
Proof. exact (EQ_MP (@lem5994524 C y x z) (@lem0)). Qed.
Lemma lem5994526 {C : Type'} (y : C) (x : C) (z : C) : term378 C y x z.
Proof. exact (EQ_MP (@lem5994525 C y x z) (@lem5994111 C x y z)). Qed.
Lemma lem5994528 (b : Prop) (a : Prop) : (a \/ b) = (term364 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5994529 {C : Type'} (x : C) (y : C) (z : C) : (term378 C y x z) = (term381 C x y z).
Proof. exact (@lem5994528 (term382 C y x z) (y = z)). Qed.
Lemma lem5994531 (a : Prop) (b : Prop) : (term383 a b) = (term384 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5994532 {C : Type'} (y : C) (x : C) (z : C) : (term385 C y x z) = (term386 C y x z).
Proof. exact (@lem5994531 (term375 C x y) (term375 C x z)). Qed.
Lemma lem5994534 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5994535 {C : Type'} (x : C) (y : C) : (term387 C x y) = (x = y).
Proof. exact (@lem5994534 (x = y)). Qed.
Lemma lem5994536 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5994537 {C : Type'} (x : C) (y : C) : (term388 C x y) = (term389 C x y).
Proof. exact (MK_COMB (@lem5994536) (@lem5994535 C x y)). Qed.
Lemma lem5994539 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5994540 {C : Type'} (x : C) (z : C) : (term387 C x z) = (x = z).
Proof. exact (@lem5994539 (x = z)). Qed.
Lemma lem5994541 {C : Type'} (y : C) (x : C) (z : C) : (term386 C y x z) = (term390 C y x z).
Proof. exact (MK_COMB (@lem5994537 C x y) (@lem5994540 C x z)). Qed.
Lemma lem5994542 {C : Type'} (y : C) (x : C) (z : C) : (term385 C y x z) = (term390 C y x z).
Proof. exact (TRANS (@lem5994532 C y x z) (@lem5994541 C y x z)). Qed.
Lemma lem5994543 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5994544 {C : Type'} (y : C) (x : C) (z : C) : (term391 C y x z) = (term392 C y x z).
Proof. exact (MK_COMB (@lem5994543) (@lem5994542 C y x z)). Qed.
Lemma lem5994545 {C : Type'} (y : C) (z : C) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5994546 {C : Type'} (x : C) (y : C) (z : C) : (term381 C x y z) = (term393 C x y z).
Proof. exact (MK_COMB (@lem5994544 C y x z) (@lem5994545 C y z)). Qed.
Lemma lem5994547 {C : Type'} (x : C) (y : C) (z : C) : (term378 C y x z) = (term393 C x y z).
Proof. exact (TRANS (@lem5994529 C x y z) (@lem5994546 C x y z)). Qed.
Lemma lem5994549 {A B C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : B -> C) (h : A -> B) (s : A -> Prop) (h1 : term431 A B C) : term1034 A B C x op f g h s.
Proof. exact (conj (@lem5994427 A B C x op f g h s h1) (@lem5994436 A B C x op f g h s)). Qed.
Lemma lem5994551 {C : Type'} (x : C) (y : C) (z : C) : term393 C x y z.
Proof. exact (EQ_MP (@lem5994547 C x y z) (@lem5994526 C y x z)). Qed.
Lemma lem5994552 {C : Type'} (x : C) (y : C) (z : C) : term393 C x y z.
Proof. exact (@lem5994551 C x y z). Qed.
Lemma lem5994553 {A B C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : B -> C) (h : A -> B) (s : A -> Prop) : term1035 A B C x op f g h s.
Proof. exact (@lem5994552 C (term1029 A B C x op f g h s) (term1025 A B C x op f g h s) (term1029 A B C x op f g h s)). Qed.
Lemma lem5994556 {A B C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : B -> C) (h : A -> B) (s : A -> Prop) (h1 : term431 A B C) : (term1025 A B C x op f g h s) = (term1029 A B C x op f g h s).
Proof. exact (@lem5994553 A B C x op f g h s (@lem5994549 A B C x op f g h s h1)). Qed.
Lemma lem5994557 {A B C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : B -> C) (h : A -> B) (s : A -> Prop) (h1 : term431 A B C) : (term1025 A B C x op f g h s) = (term1029 A B C x op f g h s).
Proof. exact (@lem5994556 A B C x op f g h s h1). Qed.
Lemma lem5994558 {A B C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : B -> C) (h : A -> B) (s : A -> Prop) (h1 : term431 A B C) : term1036 A B C x op f g h s.
Proof. exact (fun h0 : term1037 A B C x op f g h s => @lem5994557 A B C x op f g h s h1). Qed.
Lemma lem5994560 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5994561 {A B C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : B -> C) (h : A -> B) (s : A -> Prop) : (term1036 A B C x op f g h s) = ((term1025 A B C x op f g h s) = (term1029 A B C x op f g h s)).
Proof. exact (@lem5994560 ((term1025 A B C x op f g h s) = (term1029 A B C x op f g h s))). Qed.
Lemma lem5994562 {A B C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : B -> C) (h : A -> B) (s : A -> Prop) (h1 : term431 A B C) : (term1025 A B C x op f g h s) = (term1029 A B C x op f g h s).
Proof. exact (EQ_MP (@lem5994561 A B C x op f g h s) (@lem5994558 A B C x op f g h s h1)). Qed.
Lemma lem5994563 {A B C : Type'} (t : B -> Prop) (x : type747 A C) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term431 A B C) (h3 : term674 A C x) (h4 : @monoidal C op) (h5 : term857 A B C f op s g h) : term1038 A B C x op f g h s.
Proof. exact (conj (@lem5994418 A B C t x f op s g h h1 h3 h4 h5) (@lem5994562 A B C x op f g h s h2)). Qed.
Lemma lem5994565 {C : Type'} (x : C) (y : C) (z : C) : term393 C x y z.
Proof. exact (EQ_MP (@lem5994547 C x y z) (@lem5994526 C y x z)). Qed.
Lemma lem5994566 {C : Type'} (x : C) (y : C) (z : C) : term393 C x y z.
Proof. exact (@lem5994565 C x y z). Qed.
Lemma lem5994567 {A B C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : B -> C) (h : A -> B) (s : A -> Prop) : term1039 A B C x op f g h s.
Proof. exact (@lem5994566 C (term1025 A B C x op f g h s) (term1026 A B C x op f g h s) (term1029 A B C x op f g h s)). Qed.
Lemma lem5994570 {A B C : Type'} (t : B -> Prop) (x : type747 A C) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term431 A B C) (h3 : term674 A C x) (h4 : @monoidal C op) (h5 : term857 A B C f op s g h) : (term1026 A B C x op f g h s) = (term1029 A B C x op f g h s).
Proof. exact (@lem5994567 A B C x op f g h s (@lem5994563 A B C t x f op s g h h1 h2 h3 h4 h5)). Qed.
Lemma lem5994571 {A B C : Type'} (t : B -> Prop) (x : type747 A C) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term431 A B C) (h3 : term674 A C x) (h4 : @monoidal C op) (h5 : term857 A B C f op s g h) : term1040 A B C x op f g h s.
Proof. exact (fun h0 : term1041 A B C x op f g h s => @lem5994570 A B C t x f op s g h h1 h2 h3 h4 h5). Qed.
Lemma lem5994573 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5994574 {A B C : Type'} (x : type747 A C) (op : type1400 C) (f : A -> C) (g : B -> C) (h : A -> B) (s : A -> Prop) : (term1040 A B C x op f g h s) = ((term1026 A B C x op f g h s) = (term1029 A B C x op f g h s)).
Proof. exact (@lem5994573 ((term1026 A B C x op f g h s) = (term1029 A B C x op f g h s))). Qed.
Lemma lem5994575 {A B C : Type'} (t : B -> Prop) (x : type747 A C) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term431 A B C) (h3 : term674 A C x) (h4 : @monoidal C op) (h5 : term857 A B C f op s g h) : (term1026 A B C x op f g h s) = (term1029 A B C x op f g h s).
Proof. exact (EQ_MP (@lem5994574 A B C x op f g h s) (@lem5994571 A B C t x f op s g h h1 h2 h3 h4 h5)). Qed.
Lemma lem5994581 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5994582 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76116 : type1400 C) (_76119 : A -> Prop) (_76118 : A -> C) : (term986 A C x _76117 _76116 _76119 _76118) = (term1042 A C x _76117 _76116 _76119 _76118).
Proof. exact (@lem5994581 (term882 A C x _76116 _76117 _76118 _76119) (term910 C _76116) ((term850 A C _76116 _76119 _76117) = (term850 A C _76116 _76119 _76118))). Qed.
Lemma lem5994598 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5994599 {A C : Type'} (_76117 : A -> C) (_76119 : A -> Prop) (_76118 : A -> C) (_76116 : type1400 C) : (term992 A C _76117 _76116 _76119 _76118) = (term993 A C _76117 _76119 _76118 _76116).
Proof. exact (@lem5994598 ((term850 A C _76116 _76119 _76117) = (term850 A C _76116 _76119 _76118)) (term910 C _76116)). Qed.
Lemma lem5994607 {A C : Type'} (x : type747 A C) (_76116 : type1400 C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) : (term1043 A C x _76116 _76117 _76118 _76119) = (term1043 A C x _76116 _76117 _76118 _76119).
Proof. exact (eq_refl (term1043 A C x _76116 _76117 _76118 _76119)). Qed.
Lemma lem5994608 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76119 : A -> Prop) (_76118 : A -> C) (_76116 : type1400 C) : (term1042 A C x _76117 _76116 _76119 _76118) = (term1044 A C x _76117 _76119 _76118 _76116).
Proof. exact (MK_COMB (@lem5994607 A C x _76116 _76117 _76118 _76119) (@lem5994599 A C _76117 _76119 _76118 _76116)). Qed.
Lemma lem5994612 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5994613 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) (_76116 : type1400 C) : (term1044 A C x _76117 _76119 _76118 _76116) = (term1045 A C x _76117 _76118 _76119 _76116).
Proof. exact (@lem5994612 ((term850 A C _76116 _76119 _76117) = (term850 A C _76116 _76119 _76118)) (term882 A C x _76116 _76117 _76118 _76119) (term910 C _76116)). Qed.
Lemma lem5994633 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) (_76116 : type1400 C) : (term1042 A C x _76117 _76116 _76119 _76118) = (term1045 A C x _76117 _76118 _76119 _76116).
Proof. exact (TRANS (@lem5994608 A C x _76117 _76119 _76118 _76116) (@lem5994613 A C x _76117 _76118 _76119 _76116)). Qed.
Lemma lem5994634 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) (_76116 : type1400 C) : (term986 A C x _76117 _76116 _76119 _76118) = (term1045 A C x _76117 _76118 _76119 _76116).
Proof. exact (TRANS (@lem5994582 A C x _76117 _76116 _76119 _76118) (@lem5994633 A C x _76117 _76118 _76119 _76116)). Qed.
Lemma lem5994635 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5994636 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) (_76116 : type1400 C) : (term1046 A C x _76117 _76116 _76119 _76118) = (term1047 A C x _76117 _76118 _76119 _76116).
Proof. exact (MK_COMB (@lem5994635) (@lem5994634 A C x _76117 _76118 _76119 _76116)). Qed.
Lemma lem5994652 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5994653 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) (_76116 : type1400 C) : (term1048 A C x _76116 _76117 _76118 _76119) = (term1049 A C x _76117 _76118 _76119 _76116).
Proof. exact (@lem5994652 (term882 A C x _76116 _76117 _76118 _76119) (term910 C _76116)). Qed.
Lemma lem5994661 {A C : Type'} (_76117 : A -> C) (_76116 : type1400 C) (_76119 : A -> Prop) (_76118 : A -> C) : (term1050 A C _76117 _76116 _76119 _76118) = (term1050 A C _76117 _76116 _76119 _76118).
Proof. exact (eq_refl (term1050 A C _76117 _76116 _76119 _76118)). Qed.
Lemma lem5994662 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) (_76116 : type1400 C) : (term1051 A C x _76116 _76117 _76118 _76119) = (term1045 A C x _76117 _76118 _76119 _76116).
Proof. exact (MK_COMB (@lem5994661 A C _76117 _76116 _76119 _76118) (@lem5994653 A C x _76117 _76118 _76119 _76116)). Qed.
Lemma lem5994673 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) (_76116 : type1400 C) : ((term986 A C x _76117 _76116 _76119 _76118) = (term1051 A C x _76116 _76117 _76118 _76119)) = ((term1045 A C x _76117 _76118 _76119 _76116) = (term1045 A C x _76117 _76118 _76119 _76116)).
Proof. exact (MK_COMB (@lem5994636 A C x _76117 _76118 _76119 _76116) (@lem5994662 A C x _76117 _76118 _76119 _76116)). Qed.
Lemma lem5994675 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5994676 (x : Prop) : (x = x) = True.
Proof. exact (@lem5994675 Prop x). Qed.
Lemma lem5994677 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) (_76116 : type1400 C) : ((term1045 A C x _76117 _76118 _76119 _76116) = (term1045 A C x _76117 _76118 _76119 _76116)) = True.
Proof. exact (@lem5994676 (term1045 A C x _76117 _76118 _76119 _76116)). Qed.
Lemma lem5994678 {A C : Type'} (x : type747 A C) (_76116 : type1400 C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) : ((term986 A C x _76117 _76116 _76119 _76118) = (term1051 A C x _76116 _76117 _76118 _76119)) = True.
Proof. exact (TRANS (@lem5994673 A C x _76117 _76118 _76119 _76116) (@lem5994677 A C x _76117 _76118 _76119 _76116)). Qed.
Lemma lem5994679 {A C : Type'} (x : type747 A C) (_76116 : type1400 C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) : True = ((term986 A C x _76117 _76116 _76119 _76118) = (term1051 A C x _76116 _76117 _76118 _76119)).
Proof. exact (SYM (@lem5994678 A C x _76116 _76117 _76118 _76119)). Qed.
Lemma lem5994680 {A C : Type'} (x : type747 A C) (_76116 : type1400 C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) : (term986 A C x _76117 _76116 _76119 _76118) = (term1051 A C x _76116 _76117 _76118 _76119).
Proof. exact (EQ_MP (@lem5994679 A C x _76116 _76117 _76118 _76119) (@lem0)). Qed.
Lemma lem5994681 {A C : Type'} (_76116 : type1400 C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) (x : type747 A C) (h1 : term674 A C x) : term1051 A C x _76116 _76117 _76118 _76119.
Proof. exact (EQ_MP (@lem5994680 A C x _76116 _76117 _76118 _76119) (@lem5993556 A C _76117 _76116 _76119 _76118 x h1)). Qed.
Lemma lem5994683 (b : Prop) (a : Prop) : (a \/ b) = (term364 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5994684 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76116 : type1400 C) (_76119 : A -> Prop) (_76118 : A -> C) : (term1051 A C x _76116 _76117 _76118 _76119) = (term1052 A C x _76117 _76116 _76119 _76118).
Proof. exact (@lem5994683 (term1048 A C x _76116 _76117 _76118 _76119) ((term850 A C _76116 _76119 _76117) = (term850 A C _76116 _76119 _76118))). Qed.
Lemma lem5994686 (a : Prop) (b : Prop) : (term383 a b) = (term384 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5994687 {A C : Type'} (x : type747 A C) (_76116 : type1400 C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) : (term1053 A C x _76116 _76117 _76118 _76119) = (term1054 A C x _76116 _76117 _76118 _76119).
Proof. exact (@lem5994686 (term910 C _76116) (term882 A C x _76116 _76117 _76118 _76119)). Qed.
Lemma lem5994689 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5994690 {C : Type'} (_76116 : type1400 C) : (term1002 C _76116) = (@I ((C -> C -> C) -> Prop) (@monoidal C) _76116).
Proof. exact (@lem5994689 (@I ((C -> C -> C) -> Prop) (@monoidal C) _76116)). Qed.
Lemma lem5994691 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5994692 {C : Type'} (_76116 : type1400 C) : (term1003 C _76116) = (term1004 C _76116).
Proof. exact (MK_COMB (@lem5994691) (@lem5994690 C _76116)). Qed.
Lemma lem5994694 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5994695 {A C : Type'} (x : type747 A C) (_76116 : type1400 C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) : (term1055 A C x _76116 _76117 _76118 _76119) = ((term875 A C x _76116 _76117 _76118 _76119) = (term878 A C x _76116 _76117 _76118 _76119)).
Proof. exact (@lem5994694 ((term875 A C x _76116 _76117 _76118 _76119) = (term878 A C x _76116 _76117 _76118 _76119))). Qed.
Lemma lem5994696 {A C : Type'} (x : type747 A C) (_76116 : type1400 C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) : (term1054 A C x _76116 _76117 _76118 _76119) = (term1056 A C x _76116 _76117 _76118 _76119).
Proof. exact (MK_COMB (@lem5994692 C _76116) (@lem5994695 A C x _76116 _76117 _76118 _76119)). Qed.
Lemma lem5994697 {A C : Type'} (x : type747 A C) (_76116 : type1400 C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) : (term1053 A C x _76116 _76117 _76118 _76119) = (term1056 A C x _76116 _76117 _76118 _76119).
Proof. exact (TRANS (@lem5994687 A C x _76116 _76117 _76118 _76119) (@lem5994696 A C x _76116 _76117 _76118 _76119)). Qed.
Lemma lem5994698 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5994699 {A C : Type'} (x : type747 A C) (_76116 : type1400 C) (_76117 : A -> C) (_76118 : A -> C) (_76119 : A -> Prop) : (term1057 A C x _76116 _76117 _76118 _76119) = (term1058 A C x _76116 _76117 _76118 _76119).
Proof. exact (MK_COMB (@lem5994698) (@lem5994697 A C x _76116 _76117 _76118 _76119)). Qed.
Lemma lem5994700 {A C : Type'} (_76117 : A -> C) (_76116 : type1400 C) (_76119 : A -> Prop) (_76118 : A -> C) : ((term850 A C _76116 _76119 _76117) = (term850 A C _76116 _76119 _76118)) = ((term850 A C _76116 _76119 _76117) = (term850 A C _76116 _76119 _76118)).
Proof. exact (eq_refl ((term850 A C _76116 _76119 _76117) = (term850 A C _76116 _76119 _76118))). Qed.
Lemma lem5994701 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76116 : type1400 C) (_76119 : A -> Prop) (_76118 : A -> C) : (term1052 A C x _76117 _76116 _76119 _76118) = (term1059 A C x _76117 _76116 _76119 _76118).
Proof. exact (MK_COMB (@lem5994699 A C x _76116 _76117 _76118 _76119) (@lem5994700 A C _76117 _76116 _76119 _76118)). Qed.
Lemma lem5994702 {A C : Type'} (x : type747 A C) (_76117 : A -> C) (_76116 : type1400 C) (_76119 : A -> Prop) (_76118 : A -> C) : (term1051 A C x _76116 _76117 _76118 _76119) = (term1059 A C x _76117 _76116 _76119 _76118).
Proof. exact (TRANS (@lem5994684 A C x _76117 _76116 _76119 _76118) (@lem5994701 A C x _76117 _76116 _76119 _76118)). Qed.
Lemma lem5994704 {A B C : Type'} (t : B -> Prop) (x : type747 A C) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term431 A B C) (h3 : term674 A C x) (h4 : @monoidal C op) (h5 : term857 A B C f op s g h) : term1060 A B C x op f g h s.
Proof. exact (conj (@lem5994200 C op h4) (@lem5994575 A B C t x f op s g h h1 h2 h3 h4 h5)). Qed.
Lemma lem5994706 {A C : Type'} (_76117 : A -> C) (_76116 : type1400 C) (_76119 : A -> Prop) (_76118 : A -> C) (x : type747 A C) (h1 : term674 A C x) : term1059 A C x _76117 _76116 _76119 _76118.
Proof. exact (EQ_MP (@lem5994702 A C x _76117 _76116 _76119 _76118) (@lem5994681 A C _76116 _76117 _76118 _76119 x h1)). Qed.
Lemma lem5994707 {A C : Type'} (_76117 : A -> C) (_76116 : type1400 C) (_76119 : A -> Prop) (_76118 : A -> C) (x : type747 A C) (h1 : term674 A C x) : term1059 A C x _76117 _76116 _76119 _76118.
Proof. exact (@lem5994706 A C _76117 _76116 _76119 _76118 x h1). Qed.
Lemma lem5994708 {A B C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (x : type747 A C) (h1 : term674 A C x) : term1061 A B C x f op s g h.
Proof. exact (@lem5994707 A C f op s (term851 A B C g h) x h1). Qed.
Lemma lem5994711 {A B C : Type'} (t : B -> Prop) (x : type747 A C) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term431 A B C) (h3 : term674 A C x) (h4 : @monoidal C op) (h5 : term857 A B C f op s g h) : (term850 A C op s f) = (term854 A B C op s g h).
Proof. exact (@lem5994708 A B C f op s g h x h3 (@lem5994704 A B C t x f op s g h h1 h2 h3 h4 h5)). Qed.
Lemma lem5994712 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : type747 A C) (op : type1400 C) (h1 : term38 A B C s t g h f) (h2 : term431 A B C) (h3 : term674 A C x) (h4 : @monoidal C op) : term1062 A B C f op s g h.
Proof. exact (fun h0 : term857 A B C f op s g h => @lem5994711 A B C t x f op s g h h1 h2 h3 h4 h0). Qed.
Lemma lem5994714 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5994715 {A B C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term1062 A B C f op s g h) = ((term850 A C op s f) = (term854 A B C op s g h)).
Proof. exact (@lem5994714 ((term850 A C op s f) = (term854 A B C op s g h))). Qed.
Lemma lem5994716 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : type747 A C) (op : type1400 C) (h1 : term38 A B C s t g h f) (h2 : term431 A B C) (h3 : term674 A C x) (h4 : @monoidal C op) : (term850 A C op s f) = (term854 A B C op s g h).
Proof. exact (EQ_MP (@lem5994715 A B C f op s g h) (@lem5994712 A B C s t g h f x op h1 h2 h3 h4)). Qed.
Lemma lem5994719 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5994721 {A B C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term857 A B C f op s g h) = (term1063 A B C f op s g h).
Proof. exact (@lem5994719 ((term850 A C op s f) = (term854 A B C op s g h))). Qed.
Lemma lem5994724 {A B C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term427 A B C f op s g h) : term1063 A B C f op s g h.
Proof. exact (EQ_MP (@lem5994721 A B C f op s g h) (@lem5993454 A B C f op s g h h1)). Qed.
Lemma lem5994727 {A B C : Type'} (t : B -> Prop) (x : type747 A C) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term431 A B C) (h3 : term674 A C x) (h4 : @monoidal C op) (h5 : term427 A B C f op s g h) : False.
Proof. exact (@lem5994724 A B C f op s g h h5 (@lem5994716 A B C s t g h f x op h1 h2 h3 h4)). Qed.
Lemma lem5994728 {A B C : Type'} (t : B -> Prop) (x : type747 A C) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term431 A B C) (h3 : term674 A C x) (h4 : @monoidal C op) (h5 : term427 A B C f op s g h) : term410.
Proof. exact (fun h0 : ~ False => @lem5994727 A B C t x f op s g h h1 h2 h3 h4 h5). Qed.
Lemma lem5994730 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5994731 : term410 = False.
Proof. exact (@lem5994730 False). Qed.
Lemma lem5994732 {A B C : Type'} (t : B -> Prop) (x : type747 A C) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term431 A B C) (h3 : term674 A C x) (h4 : @monoidal C op) (h5 : term427 A B C f op s g h) : False.
Proof. exact (EQ_MP (@lem5994731) (@lem5994728 A B C t x f op s g h h1 h2 h3 h4 h5)). Qed.
Lemma lem5994733 {A B C : Type'} (t : B -> Prop) (x : type747 A C) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term431 A B C) (h4 : term674 A C x) (h5 : @monoidal C op) (h6 : term427 A B C f op s g h) : False.
Proof. exact (ex_elim (@lem5990406 A B t s h h2) (fun x''' : B -> A => fun h0 : term209 A B t s h x''' => @lem5994732 A B C t x f op s g h h1 h3 h4 h5 h6)). Qed.
Lemma lem5994734 {A B C : Type'} (t : B -> Prop) (x : type747 A C) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term431 A B C) (h4 : term428 A B) (h5 : term674 A C x) (h6 : @monoidal C op) (h7 : term427 A B C f op s g h) : False.
Proof. exact (ex_elim (@lem5990913 A B h4) (fun x'' : type747 A B => fun h0 : term676 A B x'' => @lem5994733 A B C t x f op s g h h1 h2 h3 h5 h6 h7)). Qed.
Lemma lem5994735 {A B C : Type'} (t : B -> Prop) (x : type747 A C) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term431 A B C) (h4 : term428 A B) (h5 : term429 B) (h6 : term674 A C x) (h7 : @monoidal C op) (h8 : term427 A B C f op s g h) : False.
Proof. exact (ex_elim (@lem5991293 B h5) (fun x' : type396 B => fun h0 : term827 B x' => @lem5994734 A B C t x f op s g h h1 h2 h3 h4 h6 h7 h8)). Qed.
Lemma lem5994736 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term431 A B C) (h4 : term428 A B) (h5 : term429 B) (h6 : term428 A C) (h7 : @monoidal C op) (h8 : term427 A B C f op s g h) : False.
Proof. exact (ex_elim (@lem5991673 A C h6) (fun x : type747 A C => fun h0 : term676 A C x => @lem5994735 A B C t x f op s g h h1 h2 h3 h4 h5 h0 h7 h8)). Qed.
Lemma lem5994737 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term431 A B C) (h4 : term428 A B) (h5 : term429 B) (h6 : term428 A C) (h7 : @monoidal C op) (h8 : term427 A B C f op s g h) : (term431 A B C) = False.
Proof. exact (prop_ext (fun h9 : term431 A B C => @lem5994736 A B C t f op s g h h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem5990533 A B C h3)). Qed.
Lemma lem5994738 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term431 A B C) (h4 : term428 A B) (h5 : term429 B) (h6 : term428 A C) (h7 : @monoidal C op) (h8 : term427 A B C f op s g h) : False.
Proof. exact (EQ_MP (@lem5994737 A B C t f op s g h h1 h2 h3 h4 h5 h6 h7 h8) (@lem5990533 A B C h3)). Qed.
Lemma lem5994739 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term431 A B C) (h4 : term428 A B) (h5 : term429 B) (h6 : term428 A C) (h7 : @monoidal C op) (h8 : term427 A B C f op s g h) : (term427 A B C f op s g h) = False.
Proof. exact (prop_ext (fun h9 : term427 A B C f op s g h => @lem5994738 A B C t f op s g h h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem5990479 A B C f op s g h h8)). Qed.
Lemma lem5994740 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term431 A B C) (h4 : term428 A B) (h5 : term429 B) (h6 : term428 A C) (h7 : @monoidal C op) (h8 : term427 A B C f op s g h) : False.
Proof. exact (EQ_MP (@lem5994739 A B C t f op s g h h1 h2 h3 h4 h5 h6 h7 h8) (@lem5990479 A B C f op s g h h8)). Qed.
Lemma lem5994741 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term431 A B C) (h4 : term428 A B) (h5 : term429 B) (h6 : term428 A C) (h7 : @monoidal C op) (h8 : term427 A B C f op s g h) : (@monoidal C op) = False.
Proof. exact (prop_ext (fun h9 : @monoidal C op => @lem5994740 A B C t f op s g h h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem5989994 C op h7)). Qed.
Lemma lem5994742 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term431 A B C) (h4 : term428 A B) (h5 : term429 B) (h6 : term428 A C) (h7 : @monoidal C op) (h8 : term427 A B C f op s g h) : False.
Proof. exact (EQ_MP (@lem5994741 A B C t f op s g h h1 h2 h3 h4 h5 h6 h7 h8) (@lem5989994 C op h7)). Qed.
Lemma lem5994743 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term431 A B C) (h4 : term428 A B) (h5 : term429 B) (h6 : @monoidal C op) (h7 : term427 A B C f op s g h) : term436 A C.
Proof. exact (fun h0 : term428 A C => @lem5994742 A B C t f op s g h h1 h2 h3 h4 h5 h0 h6 h7). Qed.
Lemma lem5994744 {A C : Type'} : (term436 A C) = (term437 A C).
Proof. exact (@lem69 (term428 A C)). Qed.
Lemma lem5994745 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term431 A B C) (h4 : term428 A B) (h5 : term429 B) (h6 : @monoidal C op) (h7 : term427 A B C f op s g h) : term437 A C.
Proof. exact (EQ_MP (@lem5994744 A C) (@lem5994743 A B C t f op s g h h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem5994746 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term431 A B C) (h4 : term428 A B) (h5 : @monoidal C op) (h6 : term427 A B C f op s g h) : term440 A B C.
Proof. exact (fun h0 : term429 B => @lem5994745 A B C t f op s g h h1 h2 h3 h4 h0 h5 h6). Qed.
Lemma lem5994747 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term431 A B C) (h4 : @monoidal C op) (h5 : term427 A B C f op s g h) : term443 A B C.
Proof. exact (fun h0 : term428 A B => @lem5994746 A B C t f op s g h h1 h2 h3 h0 h4 h5). Qed.
Lemma lem5994748 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) (h4 : term427 A B C f op s g h) : term446 A B C.
Proof. exact (fun h0 : term431 A B C => @lem5994747 A B C t f op s g h h1 h2 h0 h3 h4). Qed.
Lemma lem5994749 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) (h4 : term427 A B C f op s g h) : term449 A B C.
Proof. exact (fun h0 : term430 A B => @lem5994748 A B C t f op s g h h1 h2 h3 h4). Qed.
Lemma lem5994750 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (op : type1400 C) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) : term452 A B C f op s g h.
Proof. exact (fun h0 : term427 A B C f op s g h => @lem5994749 A B C t f op s g h h1 h2 h3 h0). Qed.
Lemma lem5994751 {A B C : Type'} (f : A -> C) (g : B -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (op : type1400 C) (h1 : term39 A B t s h) (h2 : @monoidal C op) : term454 A B C t f op s g h.
Proof. exact (fun h0 : term38 A B C s t g h f => @lem5994750 A B C g f t s h op h0 h1 h2). Qed.
Lemma lem5994752 {A B C : Type'} (t : B -> Prop) (f : A -> C) (s : A -> Prop) (g : B -> C) (h : A -> B) (op : type1400 C) (h1 : @monoidal C op) : term456 A B C t f op s g h.
Proof. exact (fun h0 : term39 A B t s h => @lem5994751 A B C f g t s h op h0 h1). Qed.
Lemma lem5994753 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : term457 A B C t f op s g h.
Proof. exact (fun h0 : @monoidal C op => @lem5994752 A B C t f s g h op h0). Qed.
Lemma lem5994758 {A B C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : term461 A B C f op s g h.
Proof. exact (fun t : B -> Prop => @lem5994753 A B C t f op s g h). Qed.
Lemma lem5994763 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : term465 A B C op s g h.
Proof. exact (fun f : A -> C => @lem5994758 A B C f op s g h). Qed.
Lemma lem5994768 {A B C : Type'} (s : A -> Prop) (g : B -> C) (h : A -> B) : term469 A B C s g h.
Proof. exact (fun op : type1400 C => @lem5994763 A B C op s g h). Qed.
Lemma lem5994773 {A B C : Type'} (g : B -> C) (h : A -> B) : term473 A B C g h.
Proof. exact (fun s : A -> Prop => @lem5994768 A B C s g h). Qed.
Lemma lem5994778 {A B C : Type'} (h : A -> B) : term477 A B C h.
Proof. exact (fun g : B -> C => @lem5994773 A B C g h). Qed.
Lemma lem5994783 {A B C : Type'} : term481 A B C.
Proof. exact (fun h : A -> B => @lem5994778 A B C h). Qed.
Lemma lem5994784 {A B C : Type'} : term480 A B C.
Proof. exact (EQ_MP (@lem5989979 A B C) (@lem5994783 A B C)). Qed.
Lemma lem5994785 {A B C : Type'} (h : A -> B) : term1064 A B C h.
Proof. exact (@lem5994784 A B C h). Qed.
Lemma lem5994786 {A B C : Type'} (h : A -> B) : (term1064 A B C h) = (term476 A B C h).
Proof. exact (eq_refl (term1064 A B C h)). Qed.
Lemma lem5994787 {A B C : Type'} (h : A -> B) : term476 A B C h.
Proof. exact (EQ_MP (@lem5994786 A B C h) (@lem5994785 A B C h)). Qed.
Lemma lem5994788 {A B C : Type'} (h : A -> B) (g : B -> C) : term1065 A B C h g.
Proof. exact (@lem5994787 A B C h g). Qed.
Lemma lem5994789 {A B C : Type'} (g : B -> C) (h : A -> B) : (term1065 A B C h g) = (term472 A B C g h).
Proof. exact (eq_refl (term1065 A B C h g)). Qed.
Lemma lem5994790 {A B C : Type'} (g : B -> C) (h : A -> B) : term472 A B C g h.
Proof. exact (EQ_MP (@lem5994789 A B C g h) (@lem5994788 A B C h g)). Qed.
Lemma lem5994791 {A B C : Type'} (g : B -> C) (h : A -> B) (s : A -> Prop) : term1066 A B C g h s.
Proof. exact (@lem5994790 A B C g h s). Qed.
Lemma lem5994792 {A B C : Type'} (s : A -> Prop) (g : B -> C) (h : A -> B) : (term1066 A B C g h s) = (term468 A B C s g h).
Proof. exact (eq_refl (term1066 A B C g h s)). Qed.
Lemma lem5994793 {A B C : Type'} (s : A -> Prop) (g : B -> C) (h : A -> B) : term468 A B C s g h.
Proof. exact (EQ_MP (@lem5994792 A B C s g h) (@lem5994791 A B C g h s)). Qed.
Lemma lem5994794 {A B C : Type'} (s : A -> Prop) (g : B -> C) (h : A -> B) (op : type1400 C) : term1067 A B C s g h op.
Proof. exact (@lem5994793 A B C s g h op). Qed.
Lemma lem5994795 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term1067 A B C s g h op) = (term464 A B C op s g h).
Proof. exact (eq_refl (term1067 A B C s g h op)). Qed.
Lemma lem5994796 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : term464 A B C op s g h.
Proof. exact (EQ_MP (@lem5994795 A B C op s g h) (@lem5994794 A B C s g h op)). Qed.
Lemma lem5994797 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : term1068 A B C op s g h f.
Proof. exact (@lem5994796 A B C op s g h f). Qed.
Lemma lem5994798 {A B C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term1068 A B C op s g h f) = (term460 A B C f op s g h).
Proof. exact (eq_refl (term1068 A B C op s g h f)). Qed.
Lemma lem5994799 {A B C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : term460 A B C f op s g h.
Proof. exact (EQ_MP (@lem5994798 A B C f op s g h) (@lem5994797 A B C op s g h f)). Qed.
Lemma lem5994800 {A B C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (t : B -> Prop) : term1069 A B C f op s g h t.
Proof. exact (@lem5994799 A B C f op s g h t). Qed.
Lemma lem5994801 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : (term1069 A B C f op s g h t) = (term432 A B C t f op s g h).
Proof. exact (eq_refl (term1069 A B C f op s g h t)). Qed.
Lemma lem5994802 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : term432 A B C t f op s g h.
Proof. exact (EQ_MP (@lem5994801 A B C t f op s g h) (@lem5994800 A B C f op s g h t)). Qed.
Lemma lem5994804 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : term432 A B C t f op s g h.
Proof. exact (@lem5989341 A B C t f op s g h (@lem5994802 A B C t f op s g h)). Qed.
Lemma lem5994805 {A B C : Type'} (t : B -> Prop) (f : A -> C) (s : A -> Prop) (g : B -> C) (h : A -> B) (op : type1400 C) (h1 : @monoidal C op) : term455 A B C t f op s g h.
Proof. exact (@lem5994804 A B C t f op s g h (@lem5986686 C op h1)). Qed.
Lemma lem5994806 {A B C : Type'} (f : A -> C) (g : B -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (op : type1400 C) (h1 : term39 A B t s h) (h2 : @monoidal C op) : term453 A B C t f op s g h.
Proof. exact (@lem5994805 A B C t f s g h op h2 (@lem5986689 A B t s h h1)). Qed.
Lemma lem5994807 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (op : type1400 C) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) : term451 A B C f op s g h.
Proof. exact (@lem5994806 A B C f g t s h op h2 h3 (@lem5986688 A B C s t g h f h1)). Qed.
Lemma lem5994808 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) (h4 : term427 A B C f op s g h) : term448 A B C.
Proof. exact (@lem5994807 A B C g f t s h op h1 h2 h3 (@lem5989316 A B C f op s g h h4)). Qed.
Lemma lem5994809 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) (h4 : term427 A B C f op s g h) : term445 A B C.
Proof. exact (@lem5994808 A B C t f op s g h h1 h2 h3 h4 (@lem5989323 A B)). Qed.
Lemma lem5994810 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) (h4 : term427 A B C f op s g h) : term442 A B C.
Proof. exact (@lem5994809 A B C t f op s g h h1 h2 h3 h4 (@lem5989324 A B C)). Qed.
Lemma lem5994811 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) (h4 : term427 A B C f op s g h) : term439 A B C.
Proof. exact (@lem5994810 A B C t f op s g h h1 h2 h3 h4 (@lem5989319 A B)). Qed.
Lemma lem5994812 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) (h4 : term427 A B C f op s g h) : term436 A C.
Proof. exact (@lem5994811 A B C t f op s g h h1 h2 h3 h4 (@lem5989318 B)). Qed.
Lemma lem5994813 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) (h4 : term427 A B C f op s g h) : False.
Proof. exact (@lem5994812 A B C t f op s g h h1 h2 h3 h4 (@lem5989317 A C)). Qed.
Lemma lem5994814 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) (h4 : term427 A B C f op s g h) : (term427 A B C f op s g h) = False.
Proof. exact (prop_ext (fun h5 : term427 A B C f op s g h => @lem5994813 A B C t f op s g h h1 h2 h3 h4) (fun h5 : False => @lem5989316 A B C f op s g h h4)). Qed.
Lemma lem5994815 {A B C : Type'} (t : B -> Prop) (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) (h4 : term427 A B C f op s g h) : False.
Proof. exact (EQ_MP (@lem5994814 A B C t f op s g h h1 h2 h3 h4) (@lem5989316 A B C f op s g h h4)). Qed.
Lemma lem5994816 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (op : type1400 C) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) : term426 A B C f op s g h.
Proof. exact (fun h0 : term427 A B C f op s g h => @lem5994815 A B C t f op s g h h1 h2 h3 h0). Qed.
Lemma lem5994817 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (op : type1400 C) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) : (@iterate C A op s f) = (term425 A B C op s g h).
Proof. exact (EQ_MP (@lem5989315 A B C f op s g h) (@lem5994816 A B C g f t s h op h1 h2 h3)). Qed.
Lemma lem5994818 {A B C : Type'} (op : type1400 C) (h : A -> B) (s : A -> Prop) (g : B -> C) (h1 : (term425 A B C op s g h) = (term43 A B C op h s g)) : (term425 A B C op s g h) = (term43 A B C op h s g).
Proof. exact (h1). Qed.
Lemma lem5994819 {A B C : Type'} (op : type1400 C) (h : A -> B) (s : A -> Prop) (g : B -> C) (h1 : (term425 A B C op s g h) = (term43 A B C op h s g)) : (term43 A B C op h s g) = (term425 A B C op s g h).
Proof. exact (SYM (@lem5994818 A B C op h s g h1)). Qed.
Lemma lem5994820 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : (term43 A B C op h s g) = (term425 A B C op s g h)) : (term43 A B C op h s g) = (term425 A B C op s g h).
Proof. exact (h1). Qed.
Lemma lem5994821 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) (h1 : (term43 A B C op h s g) = (term425 A B C op s g h)) : (term425 A B C op s g h) = (term43 A B C op h s g).
Proof. exact (SYM (@lem5994820 A B C op s g h h1)). Qed.
Lemma lem5994822 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (h : A -> B) : ((term425 A B C op s g h) = (term43 A B C op h s g)) = ((term43 A B C op h s g) = (term425 A B C op s g h)).
Proof. exact (prop_ext (fun h1 : (term425 A B C op s g h) = (term43 A B C op h s g) => @lem5994819 A B C op h s g h1) (fun h1 : (term43 A B C op h s g) = (term425 A B C op s g h) => @lem5994821 A B C op s g h h1)). Qed.
Lemma lem5994823 {A B C : Type'} (op : type1400 C) (h : A -> B) (s : A -> Prop) (g : B -> C) : ((term43 A B C op h s g) = (term425 A B C op s g h)) = ((term425 A B C op s g h) = (term43 A B C op h s g)).
Proof. exact (SYM (@lem5994822 A B C op s g h)). Qed.
Lemma lem5994829 {A B C : Type'} (op : type1400 C) : term8 A B C op.
Proof. exact (EQ_MP (@lem5986621 A B C op) (@lem5986620 A B C op)). Qed.
Lemma lem5994830 {A B C : Type'} (op : type1400 C) : term8 A B C op.
Proof. exact (@lem5994829 A B C op). Qed.
Lemma lem5994831 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term1070 A B C op.
Proof. exact (@lem5994830 A B C op (@lem5986686 C op h1)). Qed.
Lemma lem5994832 {A B C : Type'} (op : type1400 C) (h1 : term1070 A B C op) : term1070 A B C op.
Proof. exact (h1). Qed.
Lemma lem5994833 {A B C : Type'} (f : A -> B) (op : type1400 C) (h1 : term1070 A B C op) : term1071 A B C op f.
Proof. exact (@lem5994832 A B C op h1 f). Qed.
Lemma lem5994834 {A B C : Type'} (op : type1400 C) (f : A -> B) : (term1071 A B C op f) = (term1072 A B C op f).
Proof. exact (eq_refl (term1071 A B C op f)). Qed.
Lemma lem5994835 {A B C : Type'} (f : A -> B) (op : type1400 C) (h1 : term1070 A B C op) : term1072 A B C op f.
Proof. exact (EQ_MP (@lem5994834 A B C op f) (@lem5994833 A B C f op h1)). Qed.
Lemma lem5994836 {A B C : Type'} (f : A -> B) (g : B -> C) (op : type1400 C) (h1 : term1070 A B C op) : term1073 A B C op f g.
Proof. exact (@lem5994835 A B C f op h1 g). Qed.
Lemma lem5994837 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) : (term1073 A B C op f g) = (term1074 A B C op g f).
Proof. exact (eq_refl (term1073 A B C op f g)). Qed.
Lemma lem5994838 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term1070 A B C op) : term1074 A B C op g f.
Proof. exact (EQ_MP (@lem5994837 A B C op g f) (@lem5994836 A B C f g op h1)). Qed.
Lemma lem5994839 {A B C : Type'} (g : B -> C) (f : A -> B) (s : A -> Prop) (op : type1400 C) (h1 : term1070 A B C op) : term1075 A B C op g f s.
Proof. exact (@lem5994838 A B C g f op h1 s). Qed.
Lemma lem5994840 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term1075 A B C op g f s) = (term1076 A B C op s g f).
Proof. exact (eq_refl (term1075 A B C op g f s)). Qed.
Lemma lem5994841 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term1070 A B C op) : term1076 A B C op s g f.
Proof. exact (EQ_MP (@lem5994840 A B C op s g f) (@lem5994839 A B C g f s op h1)). Qed.
Lemma lem5994842 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term1077 A B s f) : term1077 A B s f.
Proof. exact (h1). Qed.
Lemma lem5994843 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (op : type1400 C) (h1 : term1077 A B s f) (h2 : term1070 A B C op) : (term43 A B C op f s g) = (term425 A B C op s g f).
Proof. exact (@lem5994841 A B C s g f op h2 (@lem5994842 A B s f h1)). Qed.
Lemma lem5994844 {A B C : Type'} (op : type1400 C) (g : B -> C) (s : A -> Prop) (f : A -> B) (h1 : term1077 A B s f) : term1078 A B C op s g f.
Proof. exact (fun h0 : term1070 A B C op => @lem5994843 A B C g s f op h1 h0). Qed.
Lemma lem5994845 {A B C : Type'} (op : type1400 C) (h1 : term1070 A B C op) : term1070 A B C op.
Proof. exact (h1). Qed.
Lemma lem5994846 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (op : type1400 C) (h1 : term1077 A B s f) (h2 : term1070 A B C op) : (term43 A B C op f s g) = (term425 A B C op s g f).
Proof. exact (@lem5994844 A B C op g s f h1 (@lem5994845 A B C op h2)). Qed.
Lemma lem5994847 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term1070 A B C op) : term1076 A B C op s g f.
Proof. exact (fun h0 : term1077 A B s f => @lem5994846 A B C g s f op h0 h1). Qed.
Lemma lem5994848 {A B C : Type'} (s : A -> Prop) (g : B -> C) (op : type1400 C) (h1 : term1070 A B C op) : term1079 A B C op s g.
Proof. exact (fun f : A -> B => @lem5994847 A B C s g f op h1). Qed.
Lemma lem5994849 {A B C : Type'} (s : A -> Prop) (op : type1400 C) (h1 : term1070 A B C op) : term1080 A B C op s.
Proof. exact (fun g : B -> C => @lem5994848 A B C s g op h1). Qed.
Lemma lem5994850 {A B C : Type'} (op : type1400 C) (h1 : term1070 A B C op) : term1081 A B C op.
Proof. exact (fun s : A -> Prop => @lem5994849 A B C s op h1). Qed.
Lemma lem5994851 {A B C : Type'} (op : type1400 C) : term1082 A B C op.
Proof. exact (fun h0 : term1070 A B C op => @lem5994850 A B C op h0). Qed.
Lemma lem5994852 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term1081 A B C op.
Proof. exact (@lem5994851 A B C op (@lem5994831 A B C op h1)). Qed.
Lemma lem5994853 {A B C : Type'} (s : A -> Prop) (op : type1400 C) (h1 : @monoidal C op) : term1083 A B C op s.
Proof. exact (@lem5994852 A B C op h1 s). Qed.
Lemma lem5994854 {A B C : Type'} (op : type1400 C) (s : A -> Prop) : (term1083 A B C op s) = (term1080 A B C op s).
Proof. exact (eq_refl (term1083 A B C op s)). Qed.
Lemma lem5994855 {A B C : Type'} (s : A -> Prop) (op : type1400 C) (h1 : @monoidal C op) : term1080 A B C op s.
Proof. exact (EQ_MP (@lem5994854 A B C op s) (@lem5994853 A B C s op h1)). Qed.
Lemma lem5994856 {A B C : Type'} (s : A -> Prop) (g : B -> C) (op : type1400 C) (h1 : @monoidal C op) : term1084 A B C op s g.
Proof. exact (@lem5994855 A B C s op h1 g). Qed.
Lemma lem5994857 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) : (term1084 A B C op s g) = (term1079 A B C op s g).
Proof. exact (eq_refl (term1084 A B C op s g)). Qed.
Lemma lem5994858 {A B C : Type'} (s : A -> Prop) (g : B -> C) (op : type1400 C) (h1 : @monoidal C op) : term1079 A B C op s g.
Proof. exact (EQ_MP (@lem5994857 A B C op s g) (@lem5994856 A B C s g op h1)). Qed.
Lemma lem5994859 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : term1085 A B C op s g f.
Proof. exact (@lem5994858 A B C s g op h1 f). Qed.
Lemma lem5994860 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term1085 A B C op s g f) = (term1076 A B C op s g f).
Proof. exact (eq_refl (term1085 A B C op s g f)). Qed.
Lemma lem5994863 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : term1076 A B C op s g f.
Proof. exact (EQ_MP (@lem5994860 A B C op s g f) (@lem5994859 A B C s g f op h1)). Qed.
Lemma lem5994864 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : term1076 A B C op s g f.
Proof. exact (@lem5994863 A B C s g f op h1). Qed.
Lemma lem5994865 {A B C : Type'} (s : A -> Prop) (g : B -> C) (h : A -> B) (op : type1400 C) (h1 : @monoidal C op) : term1076 A B C op s g h.
Proof. exact (@lem5994864 A B C s g h op h1). Qed.
Lemma lem5994867 (p : Prop) : p = (term51 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5994868 {A B : Type'} (s : A -> Prop) (h : A -> B) : (term1077 A B s h) = (term1086 A B s h).
Proof. exact (@lem5994867 (term1077 A B s h)). Qed.
Lemma lem5994869 {A B : Type'} (s : A -> Prop) (h : A -> B) : (term1086 A B s h) = (term1077 A B s h).
Proof. exact (SYM (@lem5994868 A B s h)). Qed.
Lemma lem5994870 {A B : Type'} (s : A -> Prop) (h : A -> B) (h1 : term1087 A B s h) : term1087 A B s h.
Proof. exact (h1). Qed.
Lemma lem5994873 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) (h1 : term1088 A B C t g f s h) : term1088 A B C t g f s h.
Proof. exact (h1). Qed.
Lemma lem5994874 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) : term1089 A B C t g f s h.
Proof. exact (fun h0 : term1088 A B C t g f s h => @lem5994873 A B C t g f s h h0). Qed.
Lemma lem5994875 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) (h1 : term1089 A B C t g f s h) : term1089 A B C t g f s h.
Proof. exact (h1). Qed.
Lemma lem5994876 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) (h1 : term1088 A B C t g f s h) : term1088 A B C t g f s h.
Proof. exact (h1). Qed.
Lemma lem5994877 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) (h1 : term1088 A B C t g f s h) (h2 : term1089 A B C t g f s h) : term1088 A B C t g f s h.
Proof. exact (@lem5994875 A B C t g f s h h2 (@lem5994876 A B C t g f s h h1)). Qed.
Lemma lem5994878 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) (h1 : term1088 A B C t g f s h) : term1090 A B C t g f s h.
Proof. exact (fun h0 : term1089 A B C t g f s h => @lem5994877 A B C t g f s h h1 h0). Qed.
Lemma lem5994879 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) (h1 : term1089 A B C t g f s h) : term1089 A B C t g f s h.
Proof. exact (h1). Qed.
Lemma lem5994880 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) (h1 : term1088 A B C t g f s h) (h2 : term1089 A B C t g f s h) : term1088 A B C t g f s h.
Proof. exact (@lem5994878 A B C t g f s h h1 (@lem5994879 A B C t g f s h h2)). Qed.
Lemma lem5994881 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) (h1 : term1089 A B C t g f s h) : term1089 A B C t g f s h.
Proof. exact (fun h0 : term1088 A B C t g f s h => @lem5994880 A B C t g f s h h0 h1). Qed.
Lemma lem5994882 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) : term1091 A B C t g f s h.
Proof. exact (fun h0 : term1089 A B C t g f s h => @lem5994881 A B C t g f s h h0). Qed.
Lemma lem5994885 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) : term1089 A B C t g f s h.
Proof. exact (@lem5994882 A B C t g f s h (@lem5994874 A B C t g f s h)). Qed.
Lemma lem5994886 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) : term1089 A B C t g f s h.
Proof. exact (@lem5994885 A B C t g f s h). Qed.
Lemma lem5994928 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5994929 {A B : Type'} (s : A -> Prop) (h : A -> B) : (term1086 A B s h) = (term1092 A B s h).
Proof. exact (@lem5994928 (term1087 A B s h)). Qed.
Lemma lem5994931 (t : Prop) : (term59 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5994932 {A B : Type'} (s : A -> Prop) (h : A -> B) : (term1092 A B s h) = (term1077 A B s h).
Proof. exact (@lem5994931 (term1077 A B s h)). Qed.
Lemma lem5994937 {A B : Type'} (s : A -> Prop) (h : A -> B) : (term1086 A B s h) = (term1077 A B s h).
Proof. exact (TRANS (@lem5994929 A B s h) (@lem5994932 A B s h)). Qed.
Lemma lem5994948 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term60 A B C s t g h f) = (term60 A B C s t g h f).
Proof. exact (eq_refl (term60 A B C s t g h f)). Qed.
Lemma lem5994949 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) : (term1093 A B C t g f s h) = (term1094 A B C t g f s h).
Proof. exact (MK_COMB (@lem5994948 A B C s t g h f) (@lem5994937 A B s h)). Qed.
Lemma lem5994952 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term63 A B t s h) = (term63 A B t s h).
Proof. exact (eq_refl (term63 A B t s h)). Qed.
Lemma lem5994953 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) : (term1088 A B C t g f s h) = (term1095 A B C t g f s h).
Proof. exact (MK_COMB (@lem5994952 A B t s h) (@lem5994949 A B C t g f s h)). Qed.
Lemma lem5994956 {A B C : Type'} (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) : (term1096 A B C g f s h) = (term1097 A B C g f s h).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5994953 A B C t g f s h)). Qed.
Lemma lem5994957 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5994958 {A B C : Type'} (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) : (term1098 A B C g f s h) = (term1099 A B C g f s h).
Proof. exact (MK_COMB (@lem5994957 B) (@lem5994956 A B C g f s h)). Qed.
Lemma lem5994963 {A B C : Type'} (f : A -> C) (s : A -> Prop) (h : A -> B) : (term1100 A B C f s h) = (term1101 A B C f s h).
Proof. exact (fun_ext (fun g : B -> C => @lem5994958 A B C g f s h)). Qed.
Lemma lem5994964 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem5994965 {A B C : Type'} (f : A -> C) (s : A -> Prop) (h : A -> B) : (term1102 A B C f s h) = (term1103 A B C f s h).
Proof. exact (MK_COMB (@lem5994964 B C) (@lem5994963 A B C f s h)). Qed.
Lemma lem5994970 {A B C : Type'} (s : A -> Prop) (h : A -> B) : (term1104 A B C s h) = (term1105 A B C s h).
Proof. exact (fun_ext (fun f : A -> C => @lem5994965 A B C f s h)). Qed.
Lemma lem5994971 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem5994972 {A B C : Type'} (s : A -> Prop) (h : A -> B) : (term1106 A B C s h) = (term1107 A B C s h).
Proof. exact (MK_COMB (@lem5994971 A C) (@lem5994970 A B C s h)). Qed.
Lemma lem5994977 {A B C : Type'} (h : A -> B) : (term1108 A B C h) = (term1109 A B C h).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5994972 A B C s h)). Qed.
Lemma lem5994978 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5994979 {A B C : Type'} (h : A -> B) : (term1110 A B C h) = (term1111 A B C h).
Proof. exact (MK_COMB (@lem5994978 A) (@lem5994977 A B C h)). Qed.
Lemma lem5994984 {A B C : Type'} : (term1112 A B C) = (term1113 A B C).
Proof. exact (fun_ext (fun h : A -> B => @lem5994979 A B C h)). Qed.
Lemma lem5994985 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5994994 {A B C : Type'} : (term1114 A B C) = (term1115 A B C).
Proof. exact (MK_COMB (@lem5994985 A B) (@lem5994984 A B C)). Qed.
Lemma lem5995007 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : A) : (term1116 A B s h x y) = (term1116 A B s h x y).
Proof. exact (eq_refl (term1116 A B s h x y)). Qed.
Lemma lem5995008 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) : (term1117 A B s h x) = (term1117 A B s h x).
Proof. exact (fun_ext (fun y : A => @lem5995007 A B s h x y)). Qed.
Lemma lem5995009 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5995010 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) : (term1118 A B s h x) = (term1118 A B s h x).
Proof. exact (MK_COMB (@lem5995009 A) (@lem5995008 A B s h x)). Qed.
Lemma lem5995011 {A B : Type'} (s : A -> Prop) (h : A -> B) : (term1119 A B s h) = (term1119 A B s h).
Proof. exact (fun_ext (fun x : A => @lem5995010 A B s h x)). Qed.
Lemma lem5995012 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5995013 {A B : Type'} (s : A -> Prop) (h : A -> B) : (term1077 A B s h) = (term1077 A B s h).
Proof. exact (MK_COMB (@lem5995012 A) (@lem5995011 A B s h)). Qed.
Lemma lem5995022 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term94 A B C s t g h f x) = (term94 A B C s t g h f x).
Proof. exact (eq_refl (term94 A B C s t g h f x)). Qed.
Lemma lem5995023 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term95 A B C s t g h f) = (term95 A B C s t g h f).
Proof. exact (fun_ext (fun x : A => @lem5995022 A B C s t g h f x)). Qed.
Lemma lem5995024 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5995025 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term38 A B C s t g h f) = (term38 A B C s t g h f).
Proof. exact (MK_COMB (@lem5995024 A) (@lem5995023 A B C s t g h f)). Qed.
Lemma lem5995026 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5995027 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term60 A B C s t g h f) = (term60 A B C s t g h f).
Proof. exact (MK_COMB (@lem5995026) (@lem5995025 A B C s t g h f)). Qed.
Lemma lem5995028 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) : (term1094 A B C t g f s h) = (term1094 A B C t g f s h).
Proof. exact (MK_COMB (@lem5995027 A B C s t g h f) (@lem5995013 A B s h)). Qed.
Lemma lem5995033 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term96 A B s h x y) = (term96 A B s h x y).
Proof. exact (eq_refl (term96 A B s h x y)). Qed.
Lemma lem5995034 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term97 A B s h y) = (term97 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5995033 A B s h x y)). Qed.
Lemma lem5995035 {A : Type'} : (@ex1 A) = (@ex1 A).
Proof. exact (eq_refl (@ex1 A)). Qed.
Lemma lem5995036 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term98 A B s h y) = (term98 A B s h y).
Proof. exact (MK_COMB (@lem5995035 A) (@lem5995034 A B s h y)). Qed.
Lemma lem5995039 {B : Type'} (y : B) (t : B -> Prop) : (term99 B y t) = (term99 B y t).
Proof. exact (eq_refl (term99 B y t)). Qed.
Lemma lem5995040 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term100 A B t s h y) = (term100 A B t s h y).
Proof. exact (MK_COMB (@lem5995039 B y t) (@lem5995036 A B s h y)). Qed.
Lemma lem5995041 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term101 A B t s h) = (term101 A B t s h).
Proof. exact (fun_ext (fun y : B => @lem5995040 A B t s h y)). Qed.
Lemma lem5995042 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5995043 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term39 A B t s h) = (term39 A B t s h).
Proof. exact (MK_COMB (@lem5995042 B) (@lem5995041 A B t s h)). Qed.
Lemma lem5995044 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5995045 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term63 A B t s h) = (term63 A B t s h).
Proof. exact (MK_COMB (@lem5995044) (@lem5995043 A B t s h)). Qed.
Lemma lem5995046 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) : (term1095 A B C t g f s h) = (term1095 A B C t g f s h).
Proof. exact (MK_COMB (@lem5995045 A B t s h) (@lem5995028 A B C t g f s h)). Qed.
Lemma lem5995047 {A B C : Type'} (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) : (term1097 A B C g f s h) = (term1097 A B C g f s h).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5995046 A B C t g f s h)). Qed.
Lemma lem5995048 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5995049 {A B C : Type'} (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) : (term1099 A B C g f s h) = (term1099 A B C g f s h).
Proof. exact (MK_COMB (@lem5995048 B) (@lem5995047 A B C g f s h)). Qed.
Lemma lem5995050 {A B C : Type'} (f : A -> C) (s : A -> Prop) (h : A -> B) : (term1101 A B C f s h) = (term1101 A B C f s h).
Proof. exact (fun_ext (fun g : B -> C => @lem5995049 A B C g f s h)). Qed.
Lemma lem5995051 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem5995052 {A B C : Type'} (f : A -> C) (s : A -> Prop) (h : A -> B) : (term1103 A B C f s h) = (term1103 A B C f s h).
Proof. exact (MK_COMB (@lem5995051 B C) (@lem5995050 A B C f s h)). Qed.
Lemma lem5995053 {A B C : Type'} (s : A -> Prop) (h : A -> B) : (term1105 A B C s h) = (term1105 A B C s h).
Proof. exact (fun_ext (fun f : A -> C => @lem5995052 A B C f s h)). Qed.
Lemma lem5995054 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem5995055 {A B C : Type'} (s : A -> Prop) (h : A -> B) : (term1107 A B C s h) = (term1107 A B C s h).
Proof. exact (MK_COMB (@lem5995054 A C) (@lem5995053 A B C s h)). Qed.
Lemma lem5995056 {A B C : Type'} (h : A -> B) : (term1109 A B C h) = (term1109 A B C h).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5995055 A B C s h)). Qed.
Lemma lem5995057 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5995058 {A B C : Type'} (h : A -> B) : (term1111 A B C h) = (term1111 A B C h).
Proof. exact (MK_COMB (@lem5995057 A) (@lem5995056 A B C h)). Qed.
Lemma lem5995059 {A B C : Type'} : (term1113 A B C) = (term1113 A B C).
Proof. exact (fun_ext (fun h : A -> B => @lem5995058 A B C h)). Qed.
Lemma lem5995060 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5995061 {A B C : Type'} : (term1115 A B C) = (term1115 A B C).
Proof. exact (MK_COMB (@lem5995060 A B) (@lem5995059 A B C)). Qed.
Lemma lem5995136 {A B C : Type'} : (term1114 A B C) = (term1115 A B C).
Proof. exact (TRANS (@lem5994994 A B C) (@lem5995061 A B C)). Qed.
Lemma lem5995137 {A B C : Type'} : (term1115 A B C) = (term1114 A B C).
Proof. exact (SYM (@lem5995136 A B C)). Qed.
Lemma lem5995138 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (h1 : term39 A B t s h) : term39 A B t s h.
Proof. exact (h1). Qed.
Lemma lem5995139 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term38 A B C s t g h f.
Proof. exact (h1). Qed.
Lemma lem5995142 (p : Prop) : p = (term51 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5995143 {A : Type'} (x : A) (y : A) : (x = y) = (term1120 A x y).
Proof. exact (@lem5995142 (x = y)). Qed.
Lemma lem5995144 {A : Type'} (x : A) (y : A) : (term1120 A x y) = (x = y).
Proof. exact (SYM (@lem5995143 A x y)). Qed.
Lemma lem5995145 {A : Type'} (x : A) (y : A) (h1 : term375 A x y) : term375 A x y.
Proof. exact (h1). Qed.
Lemma lem5995155 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term104 A B s h x y) = (term105 A B s h x y).
Proof. exact (@lem17045 (@IN A x s) ((h x) = y)). Qed.
Lemma lem5995160 {A : Type'} (x' : A) (x : A) : (x' = x) = (x' = x).
Proof. exact (eq_refl (x' = x)). Qed.
Lemma lem5995161 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term106 A B s h y x) = (term96 A B s h x y).
Proof. exact (eq_refl (term106 A B s h y x)). Qed.
Lemma lem5995162 {A B : Type'} (s : A -> Prop) (h : A -> B) (x' : A) (y : B) : (term106 A B s h y x') = (term96 A B s h x' y).
Proof. exact (eq_refl (term106 A B s h y x')). Qed.
Lemma lem5995163 {A B : Type'} (s : A -> Prop) (h : A -> B) (x' : A) (y : B) : (term104 A B s h x' y) = (term105 A B s h x' y).
Proof. exact (@lem5995155 A B s h x' y). Qed.
Lemma lem5995164 {A : Type'} (P : A -> Prop) : (@ex1 A P) = (term107 A P).
Proof. exact (@lem18897 A P). Qed.
Lemma lem5995165 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term98 A B s h y) = (term108 A B s h y).
Proof. exact (@lem5995164 A (term97 A B s h y)). Qed.
Lemma lem5995166 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5995167 {A B : Type'} (s : A -> Prop) (h : A -> B) (x' : A) (y : B) : (term109 A B s h y x') = (term104 A B s h x' y).
Proof. exact (MK_COMB (@lem5995166) (@lem5995162 A B s h x' y)). Qed.
Lemma lem5995168 {A B : Type'} (s : A -> Prop) (h : A -> B) (x' : A) (y : B) : (term109 A B s h y x') = (term105 A B s h x' y).
Proof. exact (TRANS (@lem5995167 A B s h x' y) (@lem5995163 A B s h x' y)). Qed.
Lemma lem5995169 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5995170 {A B : Type'} (s : A -> Prop) (h : A -> B) (x' : A) (y : B) : (term110 A B s h y x') = (term111 A B s h x' y).
Proof. exact (MK_COMB (@lem5995169) (@lem5995168 A B s h x' y)). Qed.
Lemma lem5995171 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term112 A B s h y x' x) = (term113 A B s h y x' x).
Proof. exact (MK_COMB (@lem5995170 A B s h x' y) (@lem5995160 A x' x)). Qed.
Lemma lem5995172 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5995173 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term109 A B s h y x) = (term104 A B s h x y).
Proof. exact (MK_COMB (@lem5995172) (@lem5995161 A B s h x y)). Qed.
Lemma lem5995174 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term109 A B s h y x) = (term105 A B s h x y).
Proof. exact (TRANS (@lem5995173 A B s h x y) (@lem5995155 A B s h x y)). Qed.
Lemma lem5995175 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5995176 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term110 A B s h y x) = (term111 A B s h x y).
Proof. exact (MK_COMB (@lem5995175) (@lem5995174 A B s h x y)). Qed.
Lemma lem5995177 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term114 A B s h y x' x) = (term115 A B s h y x' x).
Proof. exact (MK_COMB (@lem5995176 A B s h x y) (@lem5995171 A B s h y x' x)). Qed.
Lemma lem5995178 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term116 A B s h y x) = (term117 A B s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5995177 A B s h y x' x)). Qed.
Lemma lem5995179 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5995180 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term118 A B s h y x) = (term119 A B s h y x).
Proof. exact (MK_COMB (@lem5995179 A) (@lem5995178 A B s h y x)). Qed.
Lemma lem5995181 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term120 A B s h y) = (term121 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5995180 A B s h y x)). Qed.
Lemma lem5995182 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5995183 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term122 A B s h y) = (term123 A B s h y).
Proof. exact (MK_COMB (@lem5995182 A) (@lem5995181 A B s h y)). Qed.
Lemma lem5995184 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term106 A B s h y x) = (term96 A B s h x y).
Proof. exact (eq_refl (term106 A B s h y x)). Qed.
Lemma lem5995185 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term124 A B s h y) = (term97 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5995184 A B s h x y)). Qed.
Lemma lem5995186 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5995187 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term125 A B s h y) = (term126 A B s h y).
Proof. exact (MK_COMB (@lem5995186 A) (@lem5995185 A B s h y)). Qed.
Lemma lem5995188 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5995189 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term127 A B s h y) = (term128 A B s h y).
Proof. exact (MK_COMB (@lem5995188) (@lem5995187 A B s h y)). Qed.
Lemma lem5995190 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term108 A B s h y) = (term129 A B s h y).
Proof. exact (MK_COMB (@lem5995189 A B s h y) (@lem5995183 A B s h y)). Qed.
Lemma lem5995191 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term98 A B s h y) = (term129 A B s h y).
Proof. exact (TRANS (@lem5995165 A B s h y) (@lem5995190 A B s h y)). Qed.
Lemma lem5995193 {B : Type'} (y : B) (t : B -> Prop) : (term130 B y t) = (term130 B y t).
Proof. exact (eq_refl (term130 B y t)). Qed.
Lemma lem5995194 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term131 A B t s h y) = (term132 A B t s h y).
Proof. exact (MK_COMB (@lem5995193 B y t) (@lem5995191 A B s h y)). Qed.
Lemma lem5995195 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term100 A B t s h y) = (term131 A B t s h y).
Proof. exact (@lem17265 (@IN B y t) (term98 A B s h y)). Qed.
Lemma lem5995196 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term100 A B t s h y) = (term132 A B t s h y).
Proof. exact (TRANS (@lem5995195 A B t s h y) (@lem5995194 A B t s h y)). Qed.
Lemma lem5995197 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term101 A B t s h) = (term133 A B t s h).
Proof. exact (fun_ext (fun y : B => @lem5995196 A B t s h y)). Qed.
Lemma lem5995198 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5995199 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term39 A B t s h) = (term134 A B t s h).
Proof. exact (MK_COMB (@lem5995198 B) (@lem5995197 A B t s h)). Qed.
Lemma lem5995301 {A : Type'} (P : Prop) (Q : A -> Prop) : (term135 A P Q) = (term136 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem5995302 {A : Type'} (P : Prop) (Q : A -> Prop) : (term135 A P Q) = (term136 A P Q).
Proof. exact (@lem5995301 A P Q). Qed.
Lemma lem5995303 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term137 A B s h y x) = (term138 A B s h y x).
Proof. exact (@lem5995302 A (term105 A B s h x y) (term139 A B s h y x)). Qed.
Lemma lem5995304 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term140 A B s h y x x') = (term113 A B s h y x' x).
Proof. exact (eq_refl (term140 A B s h y x x')). Qed.
Lemma lem5995305 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term111 A B s h x y) = (term111 A B s h x y).
Proof. exact (eq_refl (term111 A B s h x y)). Qed.
Lemma lem5995306 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term141 A B s h y x x') = (term115 A B s h y x' x).
Proof. exact (MK_COMB (@lem5995305 A B s h x y) (@lem5995304 A B s h y x' x)). Qed.
Lemma lem5995307 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term142 A B s h y x) = (term117 A B s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5995306 A B s h y x' x)). Qed.
Lemma lem5995308 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5995309 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term137 A B s h y x) = (term119 A B s h y x).
Proof. exact (MK_COMB (@lem5995308 A) (@lem5995307 A B s h y x)). Qed.
Lemma lem5995310 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5995311 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term143 A B s h y x) = (term144 A B s h y x).
Proof. exact (MK_COMB (@lem5995310) (@lem5995309 A B s h y x)). Qed.
Lemma lem5995312 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term140 A B s h y x x') = (term113 A B s h y x' x).
Proof. exact (eq_refl (term140 A B s h y x x')). Qed.
Lemma lem5995313 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term145 A B s h y x) = (term139 A B s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5995312 A B s h y x' x)). Qed.
Lemma lem5995314 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5995315 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term146 A B s h y x) = (term147 A B s h y x).
Proof. exact (MK_COMB (@lem5995314 A) (@lem5995313 A B s h y x)). Qed.
Lemma lem5995316 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term111 A B s h x y) = (term111 A B s h x y).
Proof. exact (eq_refl (term111 A B s h x y)). Qed.
Lemma lem5995317 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term138 A B s h y x) = (term148 A B s h y x).
Proof. exact (MK_COMB (@lem5995316 A B s h x y) (@lem5995315 A B s h y x)). Qed.
Lemma lem5995318 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : ((term137 A B s h y x) = (term138 A B s h y x)) = ((term119 A B s h y x) = (term148 A B s h y x)).
Proof. exact (MK_COMB (@lem5995311 A B s h y x) (@lem5995317 A B s h y x)). Qed.
Lemma lem5995319 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term119 A B s h y x) = (term148 A B s h y x).
Proof. exact (EQ_MP (@lem5995318 A B s h y x) (@lem5995303 A B s h y x)). Qed.
Lemma lem5995368 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term121 A B s h y) = (term149 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5995319 A B s h y x)). Qed.
Lemma lem5995369 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5995370 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term123 A B s h y) = (term150 A B s h y).
Proof. exact (MK_COMB (@lem5995369 A) (@lem5995368 A B s h y)). Qed.
Lemma lem5995419 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term128 A B s h y) = (term128 A B s h y).
Proof. exact (eq_refl (term128 A B s h y)). Qed.
Lemma lem5995420 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term129 A B s h y) = (term151 A B s h y).
Proof. exact (MK_COMB (@lem5995419 A B s h y) (@lem5995370 A B s h y)). Qed.
Lemma lem5995421 {B : Type'} (y : B) (t : B -> Prop) : (term130 B y t) = (term130 B y t).
Proof. exact (eq_refl (term130 B y t)). Qed.
Lemma lem5995422 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term132 A B t s h y) = (term152 A B t s h y).
Proof. exact (MK_COMB (@lem5995421 B y t) (@lem5995420 A B s h y)). Qed.
Lemma lem5995423 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term133 A B t s h) = (term153 A B t s h).
Proof. exact (fun_ext (fun y : B => @lem5995422 A B t s h y)). Qed.
Lemma lem5995424 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5995425 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term134 A B t s h) = (term154 A B t s h).
Proof. exact (MK_COMB (@lem5995424 B) (@lem5995423 A B t s h)). Qed.
Lemma lem5995475 {A : Type'} (P : A -> Prop) (Q : Prop) : (term155 A P Q) = (term156 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5995476 {A : Type'} (P : A -> Prop) (Q : Prop) : (term155 A P Q) = (term156 A P Q).
Proof. exact (@lem5995475 A P Q). Qed.
Lemma lem5995477 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term157 A B s h y) = (term158 A B s h y).
Proof. exact (@lem5995476 A (term97 A B s h y) (term150 A B s h y)). Qed.
Lemma lem5995478 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term106 A B s h y x) = (term96 A B s h x y).
Proof. exact (eq_refl (term106 A B s h y x)). Qed.
Lemma lem5995479 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term124 A B s h y) = (term97 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5995478 A B s h x y)). Qed.
Lemma lem5995480 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5995481 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term125 A B s h y) = (term126 A B s h y).
Proof. exact (MK_COMB (@lem5995480 A) (@lem5995479 A B s h y)). Qed.
Lemma lem5995482 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5995483 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term127 A B s h y) = (term128 A B s h y).
Proof. exact (MK_COMB (@lem5995482) (@lem5995481 A B s h y)). Qed.
Lemma lem5995484 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term150 A B s h y) = (term150 A B s h y).
Proof. exact (eq_refl (term150 A B s h y)). Qed.
Lemma lem5995485 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term157 A B s h y) = (term151 A B s h y).
Proof. exact (MK_COMB (@lem5995483 A B s h y) (@lem5995484 A B s h y)). Qed.
Lemma lem5995486 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5995487 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term159 A B s h y) = (term160 A B s h y).
Proof. exact (MK_COMB (@lem5995486) (@lem5995485 A B s h y)). Qed.
Lemma lem5995488 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term106 A B s h y x) = (term96 A B s h x y).
Proof. exact (eq_refl (term106 A B s h y x)). Qed.
Lemma lem5995489 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5995490 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term161 A B s h y x) = (term162 A B s h x y).
Proof. exact (MK_COMB (@lem5995489) (@lem5995488 A B s h x y)). Qed.
Lemma lem5995491 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term150 A B s h y) = (term150 A B s h y).
Proof. exact (eq_refl (term150 A B s h y)). Qed.
Lemma lem5995492 {A B : Type'} (x : A) (s : A -> Prop) (h : A -> B) (y : B) : (term163 A B x s h y) = (term164 A B x s h y).
Proof. exact (MK_COMB (@lem5995490 A B s h x y) (@lem5995491 A B s h y)). Qed.
Lemma lem5995493 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term165 A B s h y) = (term166 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5995492 A B x s h y)). Qed.
Lemma lem5995494 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5995495 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term158 A B s h y) = (term167 A B s h y).
Proof. exact (MK_COMB (@lem5995494 A) (@lem5995493 A B s h y)). Qed.
Lemma lem5995496 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : ((term157 A B s h y) = (term158 A B s h y)) = ((term151 A B s h y) = (term167 A B s h y)).
Proof. exact (MK_COMB (@lem5995487 A B s h y) (@lem5995495 A B s h y)). Qed.
Lemma lem5995497 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term151 A B s h y) = (term167 A B s h y).
Proof. exact (EQ_MP (@lem5995496 A B s h y) (@lem5995477 A B s h y)). Qed.
Lemma lem5995498 {B : Type'} (y : B) (t : B -> Prop) : (term130 B y t) = (term130 B y t).
Proof. exact (eq_refl (term130 B y t)). Qed.
Lemma lem5995499 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term152 A B t s h y) = (term168 A B t s h y).
Proof. exact (MK_COMB (@lem5995498 B y t) (@lem5995497 A B s h y)). Qed.
Lemma lem5995501 {A : Type'} (P : Prop) (Q : A -> Prop) : (term169 A P Q) = (term170 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5995502 {A : Type'} (P : Prop) (Q : A -> Prop) : (term169 A P Q) = (term170 A P Q).
Proof. exact (@lem5995501 A P Q). Qed.
Lemma lem5995503 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term171 A B t s h y) = (term172 A B t s h y).
Proof. exact (@lem5995502 A (term173 B y t) (term166 A B s h y)). Qed.
Lemma lem5995504 {A B : Type'} (x : A) (s : A -> Prop) (h : A -> B) (y : B) : (term174 A B s h y x) = (term164 A B x s h y).
Proof. exact (eq_refl (term174 A B s h y x)). Qed.
Lemma lem5995505 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term175 A B s h y) = (term166 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5995504 A B x s h y)). Qed.
Lemma lem5995506 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5995507 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term176 A B s h y) = (term167 A B s h y).
Proof. exact (MK_COMB (@lem5995506 A) (@lem5995505 A B s h y)). Qed.
Lemma lem5995508 {B : Type'} (y : B) (t : B -> Prop) : (term130 B y t) = (term130 B y t).
Proof. exact (eq_refl (term130 B y t)). Qed.
Lemma lem5995509 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term171 A B t s h y) = (term168 A B t s h y).
Proof. exact (MK_COMB (@lem5995508 B y t) (@lem5995507 A B s h y)). Qed.
Lemma lem5995510 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5995511 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term177 A B t s h y) = (term178 A B t s h y).
Proof. exact (MK_COMB (@lem5995510) (@lem5995509 A B t s h y)). Qed.
Lemma lem5995512 {A B : Type'} (x : A) (s : A -> Prop) (h : A -> B) (y : B) : (term174 A B s h y x) = (term164 A B x s h y).
Proof. exact (eq_refl (term174 A B s h y x)). Qed.
Lemma lem5995513 {B : Type'} (y : B) (t : B -> Prop) : (term130 B y t) = (term130 B y t).
Proof. exact (eq_refl (term130 B y t)). Qed.
Lemma lem5995514 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (h : A -> B) (y : B) : (term179 A B t s h y x) = (term180 A B t x s h y).
Proof. exact (MK_COMB (@lem5995513 B y t) (@lem5995512 A B x s h y)). Qed.
Lemma lem5995515 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term181 A B t s h y) = (term182 A B t s h y).
Proof. exact (fun_ext (fun x : A => @lem5995514 A B t x s h y)). Qed.
Lemma lem5995516 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5995517 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term172 A B t s h y) = (term183 A B t s h y).
Proof. exact (MK_COMB (@lem5995516 A) (@lem5995515 A B t s h y)). Qed.
Lemma lem5995518 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : ((term171 A B t s h y) = (term172 A B t s h y)) = ((term168 A B t s h y) = (term183 A B t s h y)).
Proof. exact (MK_COMB (@lem5995511 A B t s h y) (@lem5995517 A B t s h y)). Qed.
Lemma lem5995519 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term168 A B t s h y) = (term183 A B t s h y).
Proof. exact (EQ_MP (@lem5995518 A B t s h y) (@lem5995503 A B t s h y)). Qed.
Lemma lem5995520 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term152 A B t s h y) = (term183 A B t s h y).
Proof. exact (TRANS (@lem5995499 A B t s h y) (@lem5995519 A B t s h y)). Qed.
Lemma lem5995521 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term153 A B t s h) = (term184 A B t s h).
Proof. exact (fun_ext (fun y : B => @lem5995520 A B t s h y)). Qed.
Lemma lem5995522 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5995523 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term154 A B t s h) = (term185 A B t s h).
Proof. exact (MK_COMB (@lem5995522 B) (@lem5995521 A B t s h)). Qed.
Lemma lem5995525 {A B : Type'} (P : type1413 A B) : (term186 A B P) = (term187 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5995526 {A B : Type'} (P : type1470 A B) : (term188 A B P) = (term189 A B P).
Proof. exact (@lem5995525 B A P). Qed.
Lemma lem5995527 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term190 A B t s h) = (term191 A B t s h).
Proof. exact (@lem5995526 A B (term192 A B t s h)). Qed.
Lemma lem5995528 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term193 A B t s h y) = (term182 A B t s h y).
Proof. exact (eq_refl (term193 A B t s h y)). Qed.
Lemma lem5995529 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5995530 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term194 A B t s h y x) = (term195 A B t s h y x).
Proof. exact (MK_COMB (@lem5995528 A B t s h y) (@lem5995529 A x)). Qed.
Lemma lem5995531 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (h : A -> B) (y : B) : (term195 A B t s h y x) = (term180 A B t x s h y).
Proof. exact (eq_refl (term195 A B t s h y x)). Qed.
Lemma lem5995532 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (h : A -> B) (y : B) : (term194 A B t s h y x) = (term180 A B t x s h y).
Proof. exact (TRANS (@lem5995530 A B t s h y x) (@lem5995531 A B t x s h y)). Qed.
Lemma lem5995533 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term196 A B t s h y) = (term182 A B t s h y).
Proof. exact (fun_ext (fun x : A => @lem5995532 A B t x s h y)). Qed.
Lemma lem5995534 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5995535 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term197 A B t s h y) = (term183 A B t s h y).
Proof. exact (MK_COMB (@lem5995534 A) (@lem5995533 A B t s h y)). Qed.
Lemma lem5995536 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term198 A B t s h) = (term184 A B t s h).
Proof. exact (fun_ext (fun y : B => @lem5995535 A B t s h y)). Qed.
Lemma lem5995537 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5995538 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term190 A B t s h) = (term185 A B t s h).
Proof. exact (MK_COMB (@lem5995537 B) (@lem5995536 A B t s h)). Qed.
Lemma lem5995539 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5995540 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term199 A B t s h) = (term200 A B t s h).
Proof. exact (MK_COMB (@lem5995539) (@lem5995538 A B t s h)). Qed.
Lemma lem5995541 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term193 A B t s h y) = (term182 A B t s h y).
Proof. exact (eq_refl (term193 A B t s h y)). Qed.
Lemma lem5995542 {A B : Type'} (x : B -> A) (y : B) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem5995543 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (x : B -> A) (y : B) : (term201 A B t s h x y) = (term202 A B t s h x y).
Proof. exact (MK_COMB (@lem5995541 A B t s h y) (@lem5995542 A B x y)). Qed.
Lemma lem5995544 {A B : Type'} (t : B -> Prop) (x : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term202 A B t s h x y) = (term203 A B t x s h y).
Proof. exact (eq_refl (term202 A B t s h x y)). Qed.
Lemma lem5995545 {A B : Type'} (t : B -> Prop) (x : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term201 A B t s h x y) = (term203 A B t x s h y).
Proof. exact (TRANS (@lem5995543 A B t s h x y) (@lem5995544 A B t x s h y)). Qed.
Lemma lem5995546 {A B : Type'} (t : B -> Prop) (x : B -> A) (s : A -> Prop) (h : A -> B) : (term204 A B t s h x) = (term205 A B t x s h).
Proof. exact (fun_ext (fun y : B => @lem5995545 A B t x s h y)). Qed.
Lemma lem5995547 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5995548 {A B : Type'} (t : B -> Prop) (x : B -> A) (s : A -> Prop) (h : A -> B) : (term206 A B t s h x) = (term207 A B t x s h).
Proof. exact (MK_COMB (@lem5995547 B) (@lem5995546 A B t x s h)). Qed.
Lemma lem5995549 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term208 A B t s h) = (term209 A B t s h).
Proof. exact (fun_ext (fun x : B -> A => @lem5995548 A B t x s h)). Qed.
Lemma lem5995550 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5995551 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term191 A B t s h) = (term210 A B t s h).
Proof. exact (MK_COMB (@lem5995550 A B) (@lem5995549 A B t s h)). Qed.
Lemma lem5995552 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : ((term190 A B t s h) = (term191 A B t s h)) = ((term185 A B t s h) = (term210 A B t s h)).
Proof. exact (MK_COMB (@lem5995540 A B t s h) (@lem5995551 A B t s h)). Qed.
Lemma lem5995553 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term185 A B t s h) = (term210 A B t s h).
Proof. exact (EQ_MP (@lem5995552 A B t s h) (@lem5995527 A B t s h)). Qed.
Lemma lem5995554 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term154 A B t s h) = (term210 A B t s h).
Proof. exact (TRANS (@lem5995523 A B t s h) (@lem5995553 A B t s h)). Qed.
Lemma lem5995555 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term134 A B t s h) = (term210 A B t s h).
Proof. exact (TRANS (@lem5995425 A B t s h) (@lem5995554 A B t s h)). Qed.
Lemma lem5995556 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term39 A B t s h) = (term210 A B t s h).
Proof. exact (TRANS (@lem5995199 A B t s h) (@lem5995555 A B t s h)). Qed.
Lemma lem5995557 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (h1 : term39 A B t s h) : term210 A B t s h.
Proof. exact (EQ_MP (@lem5995556 A B t s h) (@lem5995138 A B t s h h1)). Qed.
Lemma lem5995568 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term94 A B C s t g h f x) = (term211 A B C s t g h f x).
Proof. exact (@lem17265 (@IN A x s) (term212 A B C t g h f x)). Qed.
Lemma lem5995569 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term95 A B C s t g h f) = (term213 A B C s t g h f).
Proof. exact (fun_ext (fun x : A => @lem5995568 A B C s t g h f x)). Qed.
Lemma lem5995570 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5995623 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term38 A B C s t g h f) = (term214 A B C s t g h f).
Proof. exact (MK_COMB (@lem5995570 A) (@lem5995569 A B C s t g h f)). Qed.
Lemma lem5995624 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term214 A B C s t g h f.
Proof. exact (EQ_MP (@lem5995623 A B C s t g h f) (@lem5995139 A B C s t g h f h1)). Qed.
Lemma lem5995638 {A B : Type'} (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term1121 A B s x h y) : term1121 A B s x h y.
Proof. exact (h1). Qed.
Lemma lem5995644 {A : Type'} (x : A) (y : A) (h1 : term375 A x y) : term375 A x y.
Proof. exact (h1). Qed.
Lemma lem5995645 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x' s h) : term207 A B t x' s h.
Proof. exact (h1). Qed.
Lemma lem5995676 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term211 A B C s t g h f x) = (term211 A B C s t g h f x).
Proof. exact (eq_refl (term211 A B C s t g h f x)). Qed.
Lemma lem5995677 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term213 A B C s t g h f) = (term213 A B C s t g h f).
Proof. exact (fun_ext (fun x : A => @lem5995676 A B C s t g h f x)). Qed.
Lemma lem5995678 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5995679 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term214 A B C s t g h f) = (term214 A B C s t g h f).
Proof. exact (MK_COMB (@lem5995678 A) (@lem5995677 A B C s t g h f)). Qed.
Lemma lem5995680 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term214 A B C s t g h f.
Proof. exact (EQ_MP (@lem5995679 A B C s t g h f) (@lem5995624 A B C s t g h f h1)). Qed.
Lemma lem5995706 {A B : Type'} (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term1121 A B s x h y) : term1121 A B s x h y.
Proof. exact (h1). Qed.
Lemma lem5995714 {A : Type'} (x : A) (y : A) (h1 : term375 A x y) : term375 A x y.
Proof. exact (h1). Qed.
Lemma lem5995741 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term113 A B s h y x' x) = (term113 A B s h y x' x).
Proof. exact (eq_refl (term113 A B s h y x' x)). Qed.
Lemma lem5995742 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term139 A B s h y x) = (term139 A B s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5995741 A B s h y x' x)). Qed.
Lemma lem5995743 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5995744 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term147 A B s h y x) = (term147 A B s h y x).
Proof. exact (MK_COMB (@lem5995743 A) (@lem5995742 A B s h y x)). Qed.
Lemma lem5995765 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term111 A B s h x y) = (term111 A B s h x y).
Proof. exact (eq_refl (term111 A B s h x y)). Qed.
Lemma lem5995766 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term148 A B s h y x) = (term148 A B s h y x).
Proof. exact (MK_COMB (@lem5995765 A B s h x y) (@lem5995744 A B s h y x)). Qed.
Lemma lem5995767 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term149 A B s h y) = (term149 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5995766 A B s h y x)). Qed.
Lemma lem5995768 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5995769 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term150 A B s h y) = (term150 A B s h y).
Proof. exact (MK_COMB (@lem5995768 A) (@lem5995767 A B s h y)). Qed.
Lemma lem5995790 {A B : Type'} (s : A -> Prop) (h : A -> B) (x' : B -> A) (y : B) : (term261 A B s h x' y) = (term261 A B s h x' y).
Proof. exact (eq_refl (term261 A B s h x' y)). Qed.
Lemma lem5995791 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term262 A B x' s h y) = (term262 A B x' s h y).
Proof. exact (MK_COMB (@lem5995790 A B s h x' y) (@lem5995769 A B s h y)). Qed.
Lemma lem5995800 {B : Type'} (y : B) (t : B -> Prop) : (term130 B y t) = (term130 B y t).
Proof. exact (eq_refl (term130 B y t)). Qed.
Lemma lem5995801 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term203 A B t x' s h y) = (term203 A B t x' s h y).
Proof. exact (MK_COMB (@lem5995800 B y t) (@lem5995791 A B x' s h y)). Qed.
Lemma lem5995802 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) : (term205 A B t x' s h) = (term205 A B t x' s h).
Proof. exact (fun_ext (fun y : B => @lem5995801 A B t x' s h y)). Qed.
Lemma lem5995803 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5995804 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) : (term207 A B t x' s h) = (term207 A B t x' s h).
Proof. exact (MK_COMB (@lem5995803 B) (@lem5995802 A B t x' s h)). Qed.
Lemma lem5995805 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x' s h) : term207 A B t x' s h.
Proof. exact (EQ_MP (@lem5995804 A B t x' s h) (@lem5995645 A B t x' s h h1)). Qed.
Lemma lem5995806 {A B : Type'} (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term1121 A B s x h y) : term1122 A B s x h y.
Proof. exact (proj2 (@lem5995706 A B s x h y h1)). Qed.
Lemma lem5995827 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (x : A) : (term211 A B C s t g h f x) = (term339 A B C t s g h f x).
Proof. exact (@lem19490 (term340 A B h x t) (term173 A x s) ((term341 A B C g h x) = (f x))). Qed.
Lemma lem5995828 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term213 A B C s t g h f) = (term342 A B C t s g h f).
Proof. exact (fun_ext (fun x : A => @lem5995827 A B C t s g h f x)). Qed.
Lemma lem5995829 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5995831 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) : (term214 A B C s t g h f) = (term343 A B C t s g h f).
Proof. exact (MK_COMB (@lem5995829 A) (@lem5995828 A B C t s g h f)). Qed.
Lemma lem5995832 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term343 A B C t s g h f.
Proof. exact (EQ_MP (@lem5995831 A B C t s g h f) (@lem5995680 A B C s t g h f h1)). Qed.
Lemma lem5995836 {A : Type'} (x : A) (y : A) (h1 : term375 A x y) : term375 A x y.
Proof. exact (h1). Qed.
Lemma lem5995838 {A : Type'} (P : Prop) (Q : A -> Prop) : (term136 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5995839 {A : Type'} (P : Prop) (Q : A -> Prop) : (term136 A P Q) = (term135 A P Q).
Proof. exact (@lem5995838 A P Q). Qed.
Lemma lem5995840 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term138 A B s h y x) = (term137 A B s h y x).
Proof. exact (@lem5995839 A (term105 A B s h x y) (term139 A B s h y x)). Qed.
Lemma lem5995841 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term140 A B s h y x x') = (term113 A B s h y x' x).
Proof. exact (eq_refl (term140 A B s h y x x')). Qed.
Lemma lem5995842 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term145 A B s h y x) = (term139 A B s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5995841 A B s h y x' x)). Qed.
Lemma lem5995843 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5995844 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term146 A B s h y x) = (term147 A B s h y x).
Proof. exact (MK_COMB (@lem5995843 A) (@lem5995842 A B s h y x)). Qed.
Lemma lem5995845 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term111 A B s h x y) = (term111 A B s h x y).
Proof. exact (eq_refl (term111 A B s h x y)). Qed.
Lemma lem5995846 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term138 A B s h y x) = (term148 A B s h y x).
Proof. exact (MK_COMB (@lem5995845 A B s h x y) (@lem5995844 A B s h y x)). Qed.
Lemma lem5995847 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5995848 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term263 A B s h y x) = (term264 A B s h y x).
Proof. exact (MK_COMB (@lem5995847) (@lem5995846 A B s h y x)). Qed.
Lemma lem5995849 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term140 A B s h y x x') = (term113 A B s h y x' x).
Proof. exact (eq_refl (term140 A B s h y x x')). Qed.
Lemma lem5995850 {A B : Type'} (s : A -> Prop) (h : A -> B) (x : A) (y : B) : (term111 A B s h x y) = (term111 A B s h x y).
Proof. exact (eq_refl (term111 A B s h x y)). Qed.
Lemma lem5995851 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term141 A B s h y x x') = (term115 A B s h y x' x).
Proof. exact (MK_COMB (@lem5995850 A B s h x y) (@lem5995849 A B s h y x' x)). Qed.
Lemma lem5995852 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term142 A B s h y x) = (term117 A B s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5995851 A B s h y x' x)). Qed.
Lemma lem5995853 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5995854 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term137 A B s h y x) = (term119 A B s h y x).
Proof. exact (MK_COMB (@lem5995853 A) (@lem5995852 A B s h y x)). Qed.
Lemma lem5995855 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : ((term138 A B s h y x) = (term137 A B s h y x)) = ((term148 A B s h y x) = (term119 A B s h y x)).
Proof. exact (MK_COMB (@lem5995848 A B s h y x) (@lem5995854 A B s h y x)). Qed.
Lemma lem5995856 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term148 A B s h y x) = (term119 A B s h y x).
Proof. exact (EQ_MP (@lem5995855 A B s h y x) (@lem5995840 A B s h y x)). Qed.
Lemma lem5995857 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term149 A B s h y) = (term121 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5995856 A B s h y x)). Qed.
Lemma lem5995858 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5995859 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term150 A B s h y) = (term123 A B s h y).
Proof. exact (MK_COMB (@lem5995858 A) (@lem5995857 A B s h y)). Qed.
Lemma lem5995860 {A B : Type'} (s : A -> Prop) (h : A -> B) (x' : B -> A) (y : B) : (term261 A B s h x' y) = (term261 A B s h x' y).
Proof. exact (eq_refl (term261 A B s h x' y)). Qed.
Lemma lem5995861 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term262 A B x' s h y) = (term265 A B x' s h y).
Proof. exact (MK_COMB (@lem5995860 A B s h x' y) (@lem5995859 A B s h y)). Qed.
Lemma lem5995863 {A : Type'} (P : Prop) (Q : A -> Prop) : (term266 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5995864 {A : Type'} (P : Prop) (Q : A -> Prop) : (term266 A P Q) = (term267 A P Q).
Proof. exact (@lem5995863 A P Q). Qed.
Lemma lem5995865 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term268 A B x' s h y) = (term269 A B x' s h y).
Proof. exact (@lem5995864 A (term270 A B s h x' y) (term121 A B s h y)). Qed.
Lemma lem5995866 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term271 A B s h y x) = (term119 A B s h y x).
Proof. exact (eq_refl (term271 A B s h y x)). Qed.
Lemma lem5995867 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term272 A B s h y) = (term121 A B s h y).
Proof. exact (fun_ext (fun x : A => @lem5995866 A B s h y x)). Qed.
Lemma lem5995868 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5995869 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) : (term273 A B s h y) = (term123 A B s h y).
Proof. exact (MK_COMB (@lem5995868 A) (@lem5995867 A B s h y)). Qed.
Lemma lem5995870 {A B : Type'} (s : A -> Prop) (h : A -> B) (x' : B -> A) (y : B) : (term261 A B s h x' y) = (term261 A B s h x' y).
Proof. exact (eq_refl (term261 A B s h x' y)). Qed.
Lemma lem5995871 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term268 A B x' s h y) = (term265 A B x' s h y).
Proof. exact (MK_COMB (@lem5995870 A B s h x' y) (@lem5995869 A B s h y)). Qed.
Lemma lem5995872 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5995873 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term274 A B x' s h y) = (term275 A B x' s h y).
Proof. exact (MK_COMB (@lem5995872) (@lem5995871 A B x' s h y)). Qed.
Lemma lem5995874 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term271 A B s h y x) = (term119 A B s h y x).
Proof. exact (eq_refl (term271 A B s h y x)). Qed.
Lemma lem5995875 {A B : Type'} (s : A -> Prop) (h : A -> B) (x' : B -> A) (y : B) : (term261 A B s h x' y) = (term261 A B s h x' y).
Proof. exact (eq_refl (term261 A B s h x' y)). Qed.
Lemma lem5995876 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term276 A B x' s h y x) = (term277 A B x' s h y x).
Proof. exact (MK_COMB (@lem5995875 A B s h x' y) (@lem5995874 A B s h y x)). Qed.
Lemma lem5995877 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term278 A B x' s h y) = (term279 A B x' s h y).
Proof. exact (fun_ext (fun x : A => @lem5995876 A B x' s h y x)). Qed.
Lemma lem5995878 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5995879 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term269 A B x' s h y) = (term280 A B x' s h y).
Proof. exact (MK_COMB (@lem5995878 A) (@lem5995877 A B x' s h y)). Qed.
Lemma lem5995880 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : ((term268 A B x' s h y) = (term269 A B x' s h y)) = ((term265 A B x' s h y) = (term280 A B x' s h y)).
Proof. exact (MK_COMB (@lem5995873 A B x' s h y) (@lem5995879 A B x' s h y)). Qed.
Lemma lem5995881 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term265 A B x' s h y) = (term280 A B x' s h y).
Proof. exact (EQ_MP (@lem5995880 A B x' s h y) (@lem5995865 A B x' s h y)). Qed.
Lemma lem5995883 {A : Type'} (P : Prop) (Q : A -> Prop) : (term266 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5995884 {A : Type'} (P : Prop) (Q : A -> Prop) : (term266 A P Q) = (term267 A P Q).
Proof. exact (@lem5995883 A P Q). Qed.
Lemma lem5995885 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term281 A B x' s h y x) = (term282 A B x' s h y x).
Proof. exact (@lem5995884 A (term270 A B s h x' y) (term117 A B s h y x)). Qed.
Lemma lem5995886 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term283 A B s h y x x') = (term115 A B s h y x' x).
Proof. exact (eq_refl (term283 A B s h y x x')). Qed.
Lemma lem5995887 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term284 A B s h y x) = (term117 A B s h y x).
Proof. exact (fun_ext (fun x' : A => @lem5995886 A B s h y x' x)). Qed.
Lemma lem5995888 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5995889 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term285 A B s h y x) = (term119 A B s h y x).
Proof. exact (MK_COMB (@lem5995888 A) (@lem5995887 A B s h y x)). Qed.
Lemma lem5995890 {A B : Type'} (s : A -> Prop) (h : A -> B) (x' : B -> A) (y : B) : (term261 A B s h x' y) = (term261 A B s h x' y).
Proof. exact (eq_refl (term261 A B s h x' y)). Qed.
Lemma lem5995891 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term281 A B x' s h y x) = (term277 A B x' s h y x).
Proof. exact (MK_COMB (@lem5995890 A B s h x' y) (@lem5995889 A B s h y x)). Qed.
Lemma lem5995892 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5995893 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term286 A B x' s h y x) = (term287 A B x' s h y x).
Proof. exact (MK_COMB (@lem5995892) (@lem5995891 A B x' s h y x)). Qed.
Lemma lem5995894 {A B : Type'} (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term283 A B s h y x x') = (term115 A B s h y x' x).
Proof. exact (eq_refl (term283 A B s h y x x')). Qed.
Lemma lem5995895 {A B : Type'} (s : A -> Prop) (h : A -> B) (x' : B -> A) (y : B) : (term261 A B s h x' y) = (term261 A B s h x' y).
Proof. exact (eq_refl (term261 A B s h x' y)). Qed.
Lemma lem5995896 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x'' : A) (x : A) : (term288 A B x' s h y x x'') = (term289 A B x' s h y x'' x).
Proof. exact (MK_COMB (@lem5995895 A B s h x' y) (@lem5995894 A B s h y x'' x)). Qed.
Lemma lem5995897 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term290 A B x' s h y x) = (term291 A B x' s h y x).
Proof. exact (fun_ext (fun x'' : A => @lem5995896 A B x' s h y x'' x)). Qed.
Lemma lem5995898 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5995899 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term282 A B x' s h y x) = (term292 A B x' s h y x).
Proof. exact (MK_COMB (@lem5995898 A) (@lem5995897 A B x' s h y x)). Qed.
Lemma lem5995900 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : ((term281 A B x' s h y x) = (term282 A B x' s h y x)) = ((term277 A B x' s h y x) = (term292 A B x' s h y x)).
Proof. exact (MK_COMB (@lem5995893 A B x' s h y x) (@lem5995899 A B x' s h y x)). Qed.
Lemma lem5995901 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term277 A B x' s h y x) = (term292 A B x' s h y x).
Proof. exact (EQ_MP (@lem5995900 A B x' s h y x) (@lem5995885 A B x' s h y x)). Qed.
Lemma lem5995902 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term279 A B x' s h y) = (term293 A B x' s h y).
Proof. exact (fun_ext (fun x : A => @lem5995901 A B x' s h y x)). Qed.
Lemma lem5995903 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5995904 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term280 A B x' s h y) = (term294 A B x' s h y).
Proof. exact (MK_COMB (@lem5995903 A) (@lem5995902 A B x' s h y)). Qed.
Lemma lem5995905 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term265 A B x' s h y) = (term294 A B x' s h y).
Proof. exact (TRANS (@lem5995881 A B x' s h y) (@lem5995904 A B x' s h y)). Qed.
Lemma lem5995906 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term262 A B x' s h y) = (term294 A B x' s h y).
Proof. exact (TRANS (@lem5995861 A B x' s h y) (@lem5995905 A B x' s h y)). Qed.
Lemma lem5995907 {B : Type'} (y : B) (t : B -> Prop) : (term130 B y t) = (term130 B y t).
Proof. exact (eq_refl (term130 B y t)). Qed.
Lemma lem5995908 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term203 A B t x' s h y) = (term295 A B t x' s h y).
Proof. exact (MK_COMB (@lem5995907 B y t) (@lem5995906 A B x' s h y)). Qed.
Lemma lem5995910 {A : Type'} (P : Prop) (Q : A -> Prop) : (term136 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5995911 {A : Type'} (P : Prop) (Q : A -> Prop) : (term136 A P Q) = (term135 A P Q).
Proof. exact (@lem5995910 A P Q). Qed.
Lemma lem5995912 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term296 A B t x' s h y) = (term297 A B t x' s h y).
Proof. exact (@lem5995911 A (term173 B y t) (term293 A B x' s h y)). Qed.
Lemma lem5995913 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term298 A B x' s h y x) = (term292 A B x' s h y x).
Proof. exact (eq_refl (term298 A B x' s h y x)). Qed.
Lemma lem5995914 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term299 A B x' s h y) = (term293 A B x' s h y).
Proof. exact (fun_ext (fun x : A => @lem5995913 A B x' s h y x)). Qed.
Lemma lem5995915 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5995916 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term300 A B x' s h y) = (term294 A B x' s h y).
Proof. exact (MK_COMB (@lem5995915 A) (@lem5995914 A B x' s h y)). Qed.
Lemma lem5995917 {B : Type'} (y : B) (t : B -> Prop) : (term130 B y t) = (term130 B y t).
Proof. exact (eq_refl (term130 B y t)). Qed.
Lemma lem5995918 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term296 A B t x' s h y) = (term295 A B t x' s h y).
Proof. exact (MK_COMB (@lem5995917 B y t) (@lem5995916 A B x' s h y)). Qed.
Lemma lem5995919 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5995920 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term301 A B t x' s h y) = (term302 A B t x' s h y).
Proof. exact (MK_COMB (@lem5995919) (@lem5995918 A B t x' s h y)). Qed.
Lemma lem5995921 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term298 A B x' s h y x) = (term292 A B x' s h y x).
Proof. exact (eq_refl (term298 A B x' s h y x)). Qed.
Lemma lem5995922 {B : Type'} (y : B) (t : B -> Prop) : (term130 B y t) = (term130 B y t).
Proof. exact (eq_refl (term130 B y t)). Qed.
Lemma lem5995923 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term303 A B t x' s h y x) = (term304 A B t x' s h y x).
Proof. exact (MK_COMB (@lem5995922 B y t) (@lem5995921 A B x' s h y x)). Qed.
Lemma lem5995924 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term305 A B t x' s h y) = (term306 A B t x' s h y).
Proof. exact (fun_ext (fun x : A => @lem5995923 A B t x' s h y x)). Qed.
Lemma lem5995925 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5995926 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term297 A B t x' s h y) = (term307 A B t x' s h y).
Proof. exact (MK_COMB (@lem5995925 A) (@lem5995924 A B t x' s h y)). Qed.
Lemma lem5995927 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : ((term296 A B t x' s h y) = (term297 A B t x' s h y)) = ((term295 A B t x' s h y) = (term307 A B t x' s h y)).
Proof. exact (MK_COMB (@lem5995920 A B t x' s h y) (@lem5995926 A B t x' s h y)). Qed.
Lemma lem5995928 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term295 A B t x' s h y) = (term307 A B t x' s h y).
Proof. exact (EQ_MP (@lem5995927 A B t x' s h y) (@lem5995912 A B t x' s h y)). Qed.
Lemma lem5995930 {A : Type'} (P : Prop) (Q : A -> Prop) : (term136 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5995931 {A : Type'} (P : Prop) (Q : A -> Prop) : (term136 A P Q) = (term135 A P Q).
Proof. exact (@lem5995930 A P Q). Qed.
Lemma lem5995932 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term308 A B t x' s h y x) = (term309 A B t x' s h y x).
Proof. exact (@lem5995931 A (term173 B y t) (term291 A B x' s h y x)). Qed.
Lemma lem5995933 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x'' : A) (x : A) : (term310 A B x' s h y x x'') = (term289 A B x' s h y x'' x).
Proof. exact (eq_refl (term310 A B x' s h y x x'')). Qed.
Lemma lem5995934 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term311 A B x' s h y x) = (term291 A B x' s h y x).
Proof. exact (fun_ext (fun x'' : A => @lem5995933 A B x' s h y x'' x)). Qed.
Lemma lem5995935 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5995936 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term312 A B x' s h y x) = (term292 A B x' s h y x).
Proof. exact (MK_COMB (@lem5995935 A) (@lem5995934 A B x' s h y x)). Qed.
Lemma lem5995937 {B : Type'} (y : B) (t : B -> Prop) : (term130 B y t) = (term130 B y t).
Proof. exact (eq_refl (term130 B y t)). Qed.
Lemma lem5995938 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term308 A B t x' s h y x) = (term304 A B t x' s h y x).
Proof. exact (MK_COMB (@lem5995937 B y t) (@lem5995936 A B x' s h y x)). Qed.
Lemma lem5995939 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5995940 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term313 A B t x' s h y x) = (term314 A B t x' s h y x).
Proof. exact (MK_COMB (@lem5995939) (@lem5995938 A B t x' s h y x)). Qed.
Lemma lem5995941 {A B : Type'} (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x'' : A) (x : A) : (term310 A B x' s h y x x'') = (term289 A B x' s h y x'' x).
Proof. exact (eq_refl (term310 A B x' s h y x x'')). Qed.
Lemma lem5995942 {B : Type'} (y : B) (t : B -> Prop) : (term130 B y t) = (term130 B y t).
Proof. exact (eq_refl (term130 B y t)). Qed.
Lemma lem5995943 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x'' : A) (x : A) : (term315 A B t x' s h y x x'') = (term316 A B t x' s h y x'' x).
Proof. exact (MK_COMB (@lem5995942 B y t) (@lem5995941 A B x' s h y x'' x)). Qed.
Lemma lem5995944 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term317 A B t x' s h y x) = (term318 A B t x' s h y x).
Proof. exact (fun_ext (fun x'' : A => @lem5995943 A B t x' s h y x'' x)). Qed.
Lemma lem5995945 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5995946 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term309 A B t x' s h y x) = (term319 A B t x' s h y x).
Proof. exact (MK_COMB (@lem5995945 A) (@lem5995944 A B t x' s h y x)). Qed.
Lemma lem5995947 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : ((term308 A B t x' s h y x) = (term309 A B t x' s h y x)) = ((term304 A B t x' s h y x) = (term319 A B t x' s h y x)).
Proof. exact (MK_COMB (@lem5995940 A B t x' s h y x) (@lem5995946 A B t x' s h y x)). Qed.
Lemma lem5995948 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term304 A B t x' s h y x) = (term319 A B t x' s h y x).
Proof. exact (EQ_MP (@lem5995947 A B t x' s h y x) (@lem5995932 A B t x' s h y x)). Qed.
Lemma lem5995949 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term306 A B t x' s h y) = (term320 A B t x' s h y).
Proof. exact (fun_ext (fun x : A => @lem5995948 A B t x' s h y x)). Qed.
Lemma lem5995950 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5995951 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term307 A B t x' s h y) = (term321 A B t x' s h y).
Proof. exact (MK_COMB (@lem5995950 A) (@lem5995949 A B t x' s h y)). Qed.
Lemma lem5995952 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term295 A B t x' s h y) = (term321 A B t x' s h y).
Proof. exact (TRANS (@lem5995928 A B t x' s h y) (@lem5995951 A B t x' s h y)). Qed.
Lemma lem5995953 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (y : B) : (term203 A B t x' s h y) = (term321 A B t x' s h y).
Proof. exact (TRANS (@lem5995908 A B t x' s h y) (@lem5995952 A B t x' s h y)). Qed.
Lemma lem5995954 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) : (term205 A B t x' s h) = (term322 A B t x' s h).
Proof. exact (fun_ext (fun y : B => @lem5995953 A B t x' s h y)). Qed.
Lemma lem5995955 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5995956 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) : (term207 A B t x' s h) = (term323 A B t x' s h).
Proof. exact (MK_COMB (@lem5995955 B) (@lem5995954 A B t x' s h)). Qed.
Lemma lem5995994 {A B : Type'} (x' : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x'' : A) (x : A) : (term316 A B t x' s h y x'' x) = (term324 A B x' t s h y x'' x).
Proof. exact (@lem19490 (term270 A B s h x' y) (term173 B y t) (term115 A B s h y x'' x)). Qed.
Lemma lem5995995 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x' : A) (x : A) : (term325 A B t s h y x' x) = (term325 A B t s h y x' x).
Proof. exact (eq_refl (term325 A B t s h y x' x)). Qed.
Lemma lem5996002 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h : A -> B) (x' : B -> A) (y : B) : (term326 A B t s h x' y) = (term327 A B s t h x' y).
Proof. exact (@lem19490 (term328 A B x' y s) (term173 B y t) ((term329 A B h x' y) = y)). Qed.
Lemma lem5996003 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5996004 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h : A -> B) (x' : B -> A) (y : B) : (term330 A B t s h x' y) = (term331 A B s t h x' y).
Proof. exact (MK_COMB (@lem5996003) (@lem5996002 A B s t h x' y)). Qed.
Lemma lem5996005 {A B : Type'} (x' : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x'' : A) (x : A) : (term324 A B x' t s h y x'' x) = (term332 A B x' t s h y x'' x).
Proof. exact (MK_COMB (@lem5996004 A B s t h x' y) (@lem5995995 A B t s h y x'' x)). Qed.
Lemma lem5996007 {A B : Type'} (x' : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x'' : A) (x : A) : (term316 A B t x' s h y x'' x) = (term332 A B x' t s h y x'' x).
Proof. exact (TRANS (@lem5995994 A B x' t s h y x'' x) (@lem5996005 A B x' t s h y x'' x)). Qed.
Lemma lem5996008 {A B : Type'} (x' : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term318 A B t x' s h y x) = (term333 A B x' t s h y x).
Proof. exact (fun_ext (fun x'' : A => @lem5996007 A B x' t s h y x'' x)). Qed.
Lemma lem5996009 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5996010 {A B : Type'} (x' : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) (x : A) : (term319 A B t x' s h y x) = (term334 A B x' t s h y x).
Proof. exact (MK_COMB (@lem5996009 A) (@lem5996008 A B x' t s h y x)). Qed.
Lemma lem5996011 {A B : Type'} (x' : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term320 A B t x' s h y) = (term335 A B x' t s h y).
Proof. exact (fun_ext (fun x : A => @lem5996010 A B x' t s h y x)). Qed.
Lemma lem5996012 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5996013 {A B : Type'} (x' : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (y : B) : (term321 A B t x' s h y) = (term336 A B x' t s h y).
Proof. exact (MK_COMB (@lem5996012 A) (@lem5996011 A B x' t s h y)). Qed.
Lemma lem5996014 {A B : Type'} (x' : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term322 A B t x' s h) = (term337 A B x' t s h).
Proof. exact (fun_ext (fun y : B => @lem5996013 A B x' t s h y)). Qed.
Lemma lem5996015 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5996016 {A B : Type'} (x' : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term323 A B t x' s h) = (term338 A B x' t s h).
Proof. exact (MK_COMB (@lem5996015 B) (@lem5996014 A B x' t s h)). Qed.
Lemma lem5996017 {A B : Type'} (x' : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) : (term207 A B t x' s h) = (term338 A B x' t s h).
Proof. exact (TRANS (@lem5995956 A B t x' s h) (@lem5996016 A B x' t s h)). Qed.
Lemma lem5996018 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x' s h) : term338 A B x' t s h.
Proof. exact (EQ_MP (@lem5996017 A B x' t s h) (@lem5995805 A B t x' s h h1)). Qed.
Lemma lem5996031 {A B C : Type'} (_76271 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term348 A B C t s g h f _76271.
Proof. exact (@lem5995832 A B C s t g h f h1 _76271). Qed.
Lemma lem5996032 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (_76271 : A) : (term348 A B C t s g h f _76271) = (term339 A B C t s g h f _76271).
Proof. exact (eq_refl (term348 A B C t s g h f _76271)). Qed.
Lemma lem5996033 {A B C : Type'} (_76271 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term339 A B C t s g h f _76271.
Proof. exact (EQ_MP (@lem5996032 A B C t s g h f _76271) (@lem5996031 A B C _76271 s t g h f h1)). Qed.
Lemma lem5996034 {A B : Type'} (_76272 : B) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x' s h) : term344 A B x' t s h _76272.
Proof. exact (@lem5996018 A B t x' s h h1 _76272). Qed.
Lemma lem5996035 {A B : Type'} (x' : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (_76272 : B) : (term344 A B x' t s h _76272) = (term336 A B x' t s h _76272).
Proof. exact (eq_refl (term344 A B x' t s h _76272)). Qed.
Lemma lem5996036 {A B : Type'} (_76272 : B) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x' s h) : term336 A B x' t s h _76272.
Proof. exact (EQ_MP (@lem5996035 A B x' t s h _76272) (@lem5996034 A B _76272 t x' s h h1)). Qed.
Lemma lem5996037 {A B : Type'} (_76272 : B) (_76273 : A) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x' s h) : term345 A B x' t s h _76272 _76273.
Proof. exact (@lem5996036 A B _76272 t x' s h h1 _76273). Qed.
Lemma lem5996038 {A B : Type'} (x' : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (_76272 : B) (_76273 : A) : (term345 A B x' t s h _76272 _76273) = (term334 A B x' t s h _76272 _76273).
Proof. exact (eq_refl (term345 A B x' t s h _76272 _76273)). Qed.
Lemma lem5996039 {A B : Type'} (_76272 : B) (_76273 : A) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x' s h) : term334 A B x' t s h _76272 _76273.
Proof. exact (EQ_MP (@lem5996038 A B x' t s h _76272 _76273) (@lem5996037 A B _76272 _76273 t x' s h h1)). Qed.
Lemma lem5996040 {A B : Type'} (_76272 : B) (_76273 : A) (_76274 : A) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x' s h) : term346 A B x' t s h _76272 _76273 _76274.
Proof. exact (@lem5996039 A B _76272 _76273 t x' s h h1 _76274). Qed.
Lemma lem5996041 {A B : Type'} (x' : B -> A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (_76272 : B) (_76274 : A) (_76273 : A) : (term346 A B x' t s h _76272 _76273 _76274) = (term332 A B x' t s h _76272 _76274 _76273).
Proof. exact (eq_refl (term346 A B x' t s h _76272 _76273 _76274)). Qed.
Lemma lem5996042 {A B : Type'} (_76272 : B) (_76274 : A) (_76273 : A) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x' s h) : term332 A B x' t s h _76272 _76274 _76273.
Proof. exact (EQ_MP (@lem5996041 A B x' t s h _76272 _76274 _76273) (@lem5996040 A B _76272 _76273 _76274 t x' s h h1)). Qed.
Lemma lem5996043 {A B : Type'} (_76272 : B) (_76274 : A) (_76273 : A) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x' s h) : term325 A B t s h _76272 _76274 _76273.
Proof. exact (proj2 (@lem5996042 A B _76272 _76274 _76273 t x' s h h1)). Qed.
Lemma lem5996050 {A : Type'} (x : A) (y : A) (h1 : term375 A x y) : term375 A x y.
Proof. exact (h1). Qed.
Lemma lem5996067 {A B : Type'} (s : A -> Prop) (h : A -> B) (_76272 : B) (_76274 : A) (_76273 : A) : (term113 A B s h _76272 _76274 _76273) = (term1123 A B s h _76272 _76274 _76273).
Proof. exact (@lem5986619 (term173 A _76274 s) (term1124 A B h _76274 _76272) (_76274 = _76273)). Qed.
Lemma lem5996068 {A B : Type'} (s : A -> Prop) (h : A -> B) (_76273 : A) (_76272 : B) : (term111 A B s h _76273 _76272) = (term111 A B s h _76273 _76272).
Proof. exact (eq_refl (term111 A B s h _76273 _76272)). Qed.
Lemma lem5996069 {A B : Type'} (s : A -> Prop) (h : A -> B) (_76272 : B) (_76274 : A) (_76273 : A) : (term115 A B s h _76272 _76274 _76273) = (term1125 A B s h _76272 _76274 _76273).
Proof. exact (MK_COMB (@lem5996068 A B s h _76273 _76272) (@lem5996067 A B s h _76272 _76274 _76273)). Qed.
Lemma lem5996076 {A B : Type'} (s : A -> Prop) (h : A -> B) (_76272 : B) (_76274 : A) (_76273 : A) : (term1125 A B s h _76272 _76274 _76273) = (term1126 A B s h _76272 _76274 _76273).
Proof. exact (@lem5986619 (term173 A _76273 s) (term1124 A B h _76273 _76272) (term1123 A B s h _76272 _76274 _76273)). Qed.
Lemma lem5996077 {A B : Type'} (s : A -> Prop) (h : A -> B) (_76272 : B) (_76274 : A) (_76273 : A) : (term115 A B s h _76272 _76274 _76273) = (term1126 A B s h _76272 _76274 _76273).
Proof. exact (TRANS (@lem5996069 A B s h _76272 _76274 _76273) (@lem5996076 A B s h _76272 _76274 _76273)). Qed.
Lemma lem5996078 {B : Type'} (_76272 : B) (t : B -> Prop) : (term130 B _76272 t) = (term130 B _76272 t).
Proof. exact (eq_refl (term130 B _76272 t)). Qed.
Lemma lem5996081 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (_76272 : B) (_76274 : A) (_76273 : A) : (term325 A B t s h _76272 _76274 _76273) = (term1127 A B t s h _76272 _76274 _76273).
Proof. exact (MK_COMB (@lem5996078 B _76272 t) (@lem5996077 A B s h _76272 _76274 _76273)). Qed.
Lemma lem5996082 {A B : Type'} (_76272 : B) (_76274 : A) (_76273 : A) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x' s h) : term1127 A B t s h _76272 _76274 _76273.
Proof. exact (EQ_MP (@lem5996081 A B t s h _76272 _76274 _76273) (@lem5996043 A B _76272 _76274 _76273 t x' s h h1)). Qed.
Lemma lem5996100 {A B C : Type'} (_76271 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term357 A B s h _76271 t.
Proof. exact (proj1 (@lem5996033 A B C _76271 s t g h f h1)). Qed.
Lemma lem5996188 {A B : Type'} (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term1121 A B s x h y) : @IN A y s.
Proof. exact (proj1 (@lem5995806 A B s x h y h1)). Qed.
Lemma lem5996189 {A B : Type'} (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term1121 A B s x h y) : term359 A y s.
Proof. exact (fun h0 : term173 A y s => @lem5996188 A B s x h y h1). Qed.
Lemma lem5996191 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5996192 {A : Type'} (y : A) (s : A -> Prop) : (term359 A y s) = (@IN A y s).
Proof. exact (@lem5996191 (@IN A y s)). Qed.
Lemma lem5996193 {A B : Type'} (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term1121 A B s x h y) : @IN A y s.
Proof. exact (EQ_MP (@lem5996192 A y s) (@lem5996189 A B s x h y h1)). Qed.
Lemma lem5996199 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5996200 {A B : Type'} (h : A -> B) (t : B -> Prop) (_76271 : A) (s : A -> Prop) : (term357 A B s h _76271 t) = (term411 A B h t _76271 s).
Proof. exact (@lem5996199 (term340 A B h _76271 t) (term173 A _76271 s)). Qed.
Lemma lem5996206 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5996207 {A B : Type'} (h : A -> B) (t : B -> Prop) (_76271 : A) (s : A -> Prop) : (term412 A B s h _76271 t) = (term413 A B h t _76271 s).
Proof. exact (MK_COMB (@lem5996206) (@lem5996200 A B h t _76271 s)). Qed.
Lemma lem5996213 {A B : Type'} (h : A -> B) (t : B -> Prop) (_76271 : A) (s : A -> Prop) : (term411 A B h t _76271 s) = (term411 A B h t _76271 s).
Proof. exact (eq_refl (term411 A B h t _76271 s)). Qed.
Lemma lem5996214 {A B : Type'} (h : A -> B) (t : B -> Prop) (_76271 : A) (s : A -> Prop) : ((term357 A B s h _76271 t) = (term411 A B h t _76271 s)) = ((term411 A B h t _76271 s) = (term411 A B h t _76271 s)).
Proof. exact (MK_COMB (@lem5996207 A B h t _76271 s) (@lem5996213 A B h t _76271 s)). Qed.
Lemma lem5996216 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5996217 (x : Prop) : (x = x) = True.
Proof. exact (@lem5996216 Prop x). Qed.
Lemma lem5996218 {A B : Type'} (h : A -> B) (t : B -> Prop) (_76271 : A) (s : A -> Prop) : ((term411 A B h t _76271 s) = (term411 A B h t _76271 s)) = True.
Proof. exact (@lem5996217 (term411 A B h t _76271 s)). Qed.
Lemma lem5996219 {A B : Type'} (h : A -> B) (t : B -> Prop) (_76271 : A) (s : A -> Prop) : ((term357 A B s h _76271 t) = (term411 A B h t _76271 s)) = True.
Proof. exact (TRANS (@lem5996214 A B h t _76271 s) (@lem5996218 A B h t _76271 s)). Qed.
Lemma lem5996220 {A B : Type'} (h : A -> B) (t : B -> Prop) (_76271 : A) (s : A -> Prop) : True = ((term357 A B s h _76271 t) = (term411 A B h t _76271 s)).
Proof. exact (SYM (@lem5996219 A B h t _76271 s)). Qed.
Lemma lem5996221 {A B : Type'} (h : A -> B) (t : B -> Prop) (_76271 : A) (s : A -> Prop) : (term357 A B s h _76271 t) = (term411 A B h t _76271 s).
Proof. exact (EQ_MP (@lem5996220 A B h t _76271 s) (@lem0)). Qed.
Lemma lem5996222 {A B C : Type'} (_76271 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term411 A B h t _76271 s.
Proof. exact (EQ_MP (@lem5996221 A B h t _76271 s) (@lem5996100 A B C _76271 s t g h f h1)). Qed.
Lemma lem5996224 (b : Prop) (a : Prop) : (a \/ b) = (term364 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5996225 {A B : Type'} (s : A -> Prop) (h : A -> B) (_76271 : A) (t : B -> Prop) : (term411 A B h t _76271 s) = (term414 A B s h _76271 t).
Proof. exact (@lem5996224 (term173 A _76271 s) (term340 A B h _76271 t)). Qed.
Lemma lem5996227 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5996228 {A : Type'} (_76271 : A) (s : A -> Prop) : (term366 A _76271 s) = (@IN A _76271 s).
Proof. exact (@lem5996227 (@IN A _76271 s)). Qed.
Lemma lem5996229 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5996230 {A : Type'} (_76271 : A) (s : A -> Prop) : (term367 A _76271 s) = (term99 A _76271 s).
Proof. exact (MK_COMB (@lem5996229) (@lem5996228 A _76271 s)). Qed.
Lemma lem5996231 {A B : Type'} (h : A -> B) (_76271 : A) (t : B -> Prop) : (term340 A B h _76271 t) = (term340 A B h _76271 t).
Proof. exact (eq_refl (term340 A B h _76271 t)). Qed.
Lemma lem5996232 {A B : Type'} (s : A -> Prop) (h : A -> B) (_76271 : A) (t : B -> Prop) : (term414 A B s h _76271 t) = (term415 A B s h _76271 t).
Proof. exact (MK_COMB (@lem5996230 A _76271 s) (@lem5996231 A B h _76271 t)). Qed.
Lemma lem5996233 {A B : Type'} (s : A -> Prop) (h : A -> B) (_76271 : A) (t : B -> Prop) : (term411 A B h t _76271 s) = (term415 A B s h _76271 t).
Proof. exact (TRANS (@lem5996225 A B s h _76271 t) (@lem5996232 A B s h _76271 t)). Qed.
Lemma lem5996236 {A B C : Type'} (_76271 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term415 A B s h _76271 t.
Proof. exact (EQ_MP (@lem5996233 A B s h _76271 t) (@lem5996222 A B C _76271 s t g h f h1)). Qed.
Lemma lem5996237 {A B C : Type'} (_76271 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term415 A B s h _76271 t.
Proof. exact (@lem5996236 A B C _76271 s t g h f h1). Qed.
Lemma lem5996238 {A B C : Type'} (y : A) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term38 A B C s t g h f) : term415 A B s h y t.
Proof. exact (@lem5996237 A B C y s t g h f h1). Qed.
Lemma lem5996241 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> C) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term1121 A B s x h y) : term340 A B h y t.
Proof. exact (@lem5996238 A B C y s t g h f h1 (@lem5996193 A B s x h y h2)). Qed.
Lemma lem5996242 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> C) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term1121 A B s x h y) : term416 A B h y t.
Proof. exact (fun h0 : term354 A B h y t => @lem5996241 A B C t g f s x h y h1 h2). Qed.
Lemma lem5996244 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5996245 {A B : Type'} (h : A -> B) (y : A) (t : B -> Prop) : (term416 A B h y t) = (term340 A B h y t).
Proof. exact (@lem5996244 (term340 A B h y t)). Qed.
Lemma lem5996246 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> C) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term1121 A B s x h y) : term340 A B h y t.
Proof. exact (EQ_MP (@lem5996245 A B h y t) (@lem5996242 A B C t g f s x h y h1 h2)). Qed.
Lemma lem5996248 {A B : Type'} (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term1121 A B s x h y) : @IN A y s.
Proof. exact (proj1 (@lem5995806 A B s x h y h1)). Qed.
Lemma lem5996249 {A B : Type'} (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term1121 A B s x h y) : term359 A y s.
Proof. exact (fun h0 : term173 A y s => @lem5996248 A B s x h y h1). Qed.
Lemma lem5996251 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5996252 {A : Type'} (y : A) (s : A -> Prop) : (term359 A y s) = (@IN A y s).
Proof. exact (@lem5996251 (@IN A y s)). Qed.
Lemma lem5996253 {A B : Type'} (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term1121 A B s x h y) : @IN A y s.
Proof. exact (EQ_MP (@lem5996252 A y s) (@lem5996249 A B s x h y h1)). Qed.
Lemma lem5996255 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5996256 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5996255 B x). Qed.
Lemma lem5996257 {A B : Type'} (h : A -> B) (y : A) : (h y) = (h y).
Proof. exact (@lem5996256 B (h y)). Qed.
Lemma lem5996258 {A B : Type'} (h : A -> B) (y : A) : term1128 A B h y.
Proof. exact (fun h0 : term1129 A B h y => @lem5996257 A B h y). Qed.
Lemma lem5996260 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5996261 {A B : Type'} (h : A -> B) (y : A) : (term1128 A B h y) = ((h y) = (h y)).
Proof. exact (@lem5996260 ((h y) = (h y))). Qed.
Lemma lem5996262 {A B : Type'} (h : A -> B) (y : A) : (h y) = (h y).
Proof. exact (EQ_MP (@lem5996261 A B h y) (@lem5996258 A B h y)). Qed.
Lemma lem5996264 {A B : Type'} (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term1121 A B s x h y) : @IN A x s.
Proof. exact (proj1 (@lem5995706 A B s x h y h1)). Qed.
Lemma lem5996265 {A B : Type'} (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term1121 A B s x h y) : term359 A x s.
Proof. exact (fun h0 : term173 A x s => @lem5996264 A B s x h y h1). Qed.
Lemma lem5996267 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5996268 {A : Type'} (x : A) (s : A -> Prop) : (term359 A x s) = (@IN A x s).
Proof. exact (@lem5996267 (@IN A x s)). Qed.
Lemma lem5996269 {A B : Type'} (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term1121 A B s x h y) : @IN A x s.
Proof. exact (EQ_MP (@lem5996268 A x s) (@lem5996265 A B s x h y h1)). Qed.
Lemma lem5996271 {A B : Type'} (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term1121 A B s x h y) : (h x) = (h y).
Proof. exact (proj2 (@lem5995806 A B s x h y h1)). Qed.
Lemma lem5996272 {A B : Type'} (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term1121 A B s x h y) : term1130 A B x h y.
Proof. exact (fun h0 : term1131 A B x h y => @lem5996271 A B s x h y h1). Qed.
Lemma lem5996274 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5996275 {A B : Type'} (x : A) (h : A -> B) (y : A) : (term1130 A B x h y) = ((h x) = (h y)).
Proof. exact (@lem5996274 ((h x) = (h y))). Qed.
Lemma lem5996276 {A B : Type'} (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term1121 A B s x h y) : (h x) = (h y).
Proof. exact (EQ_MP (@lem5996275 A B x h y) (@lem5996272 A B s x h y h1)). Qed.
Lemma lem5996282 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5996283 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (_76272 : B) (_76274 : A) (_76273 : A) : (term1127 A B t s h _76272 _76274 _76273) = (term1132 A B t s h _76272 _76274 _76273).
Proof. exact (@lem5996282 (term173 A _76273 s) (term173 B _76272 t) (term1133 A B s h _76272 _76274 _76273)). Qed.
Lemma lem5996297 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5996298 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (_76272 : B) (_76274 : A) (_76273 : A) : (term1134 A B t s h _76272 _76274 _76273) = (term1135 A B t s h _76272 _76274 _76273).
Proof. exact (@lem5996297 (term1124 A B h _76273 _76272) (term173 B _76272 t) (term1123 A B s h _76272 _76274 _76273)). Qed.
Lemma lem5996314 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5996315 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h : A -> B) (_76272 : B) (_76274 : A) (_76273 : A) : (term1136 A B t s h _76272 _76274 _76273) = (term1137 A B s t h _76272 _76274 _76273).
Proof. exact (@lem5996314 (term173 A _76274 s) (term173 B _76272 t) (term1138 A B h _76272 _76274 _76273)). Qed.
Lemma lem5996329 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5996330 {A B : Type'} (h : A -> B) (_76272 : B) (t : B -> Prop) (_76274 : A) (_76273 : A) : (term1139 A B t h _76272 _76274 _76273) = (term1140 A B h _76272 t _76274 _76273).
Proof. exact (@lem5996329 (term1124 A B h _76274 _76272) (term173 B _76272 t) (_76274 = _76273)). Qed.
Lemma lem5996346 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5996347 {A B : Type'} (_76274 : A) (_76273 : A) (_76272 : B) (t : B -> Prop) : (term1141 A B _76272 t _76274 _76273) = (term1142 A B _76274 _76273 _76272 t).
Proof. exact (@lem5996346 (_76274 = _76273) (term173 B _76272 t)). Qed.
Lemma lem5996355 {A B : Type'} (h : A -> B) (_76274 : A) (_76272 : B) : (term1143 A B h _76274 _76272) = (term1143 A B h _76274 _76272).
Proof. exact (eq_refl (term1143 A B h _76274 _76272)). Qed.
Lemma lem5996356 {A B : Type'} (h : A -> B) (_76274 : A) (_76273 : A) (_76272 : B) (t : B -> Prop) : (term1140 A B h _76272 t _76274 _76273) = (term1144 A B h _76274 _76273 _76272 t).
Proof. exact (MK_COMB (@lem5996355 A B h _76274 _76272) (@lem5996347 A B _76274 _76273 _76272 t)). Qed.
Lemma lem5996360 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5996361 {A B : Type'} (_76273 : A) (h : A -> B) (_76274 : A) (_76272 : B) (t : B -> Prop) : (term1144 A B h _76274 _76273 _76272 t) = (term1145 A B _76273 h _76274 _76272 t).
Proof. exact (@lem5996360 (_76274 = _76273) (term1124 A B h _76274 _76272) (term173 B _76272 t)). Qed.
Lemma lem5996381 {A B : Type'} (_76273 : A) (h : A -> B) (_76274 : A) (_76272 : B) (t : B -> Prop) : (term1140 A B h _76272 t _76274 _76273) = (term1145 A B _76273 h _76274 _76272 t).
Proof. exact (TRANS (@lem5996356 A B h _76274 _76273 _76272 t) (@lem5996361 A B _76273 h _76274 _76272 t)). Qed.
Lemma lem5996382 {A B : Type'} (_76273 : A) (h : A -> B) (_76274 : A) (_76272 : B) (t : B -> Prop) : (term1139 A B t h _76272 _76274 _76273) = (term1145 A B _76273 h _76274 _76272 t).
Proof. exact (TRANS (@lem5996330 A B h _76272 t _76274 _76273) (@lem5996381 A B _76273 h _76274 _76272 t)). Qed.
Lemma lem5996383 {A : Type'} (_76274 : A) (s : A -> Prop) : (term130 A _76274 s) = (term130 A _76274 s).
Proof. exact (eq_refl (term130 A _76274 s)). Qed.
Lemma lem5996384 {A B : Type'} (s : A -> Prop) (_76273 : A) (h : A -> B) (_76274 : A) (_76272 : B) (t : B -> Prop) : (term1137 A B s t h _76272 _76274 _76273) = (term1146 A B s _76273 h _76274 _76272 t).
Proof. exact (MK_COMB (@lem5996383 A _76274 s) (@lem5996382 A B _76273 h _76274 _76272 t)). Qed.
Lemma lem5996388 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5996389 {A B : Type'} (_76273 : A) (s : A -> Prop) (h : A -> B) (_76274 : A) (_76272 : B) (t : B -> Prop) : (term1146 A B s _76273 h _76274 _76272 t) = (term1147 A B _76273 s h _76274 _76272 t).
Proof. exact (@lem5996388 (_76274 = _76273) (term173 A _76274 s) (term1148 A B h _76274 _76272 t)). Qed.
Lemma lem5996405 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5996406 {A B : Type'} (h : A -> B) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1149 A B s h _76274 _76272 t) = (term1150 A B h _76274 s _76272 t).
Proof. exact (@lem5996405 (term1124 A B h _76274 _76272) (term173 A _76274 s) (term173 B _76272 t)). Qed.
Lemma lem5996424 {A : Type'} (_76274 : A) (_76273 : A) : (term1151 A _76274 _76273) = (term1151 A _76274 _76273).
Proof. exact (eq_refl (term1151 A _76274 _76273)). Qed.
Lemma lem5996425 {A B : Type'} (_76273 : A) (h : A -> B) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1147 A B _76273 s h _76274 _76272 t) = (term1152 A B _76273 h _76274 s _76272 t).
Proof. exact (MK_COMB (@lem5996424 A _76274 _76273) (@lem5996406 A B h _76274 s _76272 t)). Qed.
Lemma lem5996436 {A B : Type'} (_76273 : A) (h : A -> B) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1146 A B s _76273 h _76274 _76272 t) = (term1152 A B _76273 h _76274 s _76272 t).
Proof. exact (TRANS (@lem5996389 A B _76273 s h _76274 _76272 t) (@lem5996425 A B _76273 h _76274 s _76272 t)). Qed.
Lemma lem5996437 {A B : Type'} (_76273 : A) (h : A -> B) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1137 A B s t h _76272 _76274 _76273) = (term1152 A B _76273 h _76274 s _76272 t).
Proof. exact (TRANS (@lem5996384 A B s _76273 h _76274 _76272 t) (@lem5996436 A B _76273 h _76274 s _76272 t)). Qed.
Lemma lem5996438 {A B : Type'} (_76273 : A) (h : A -> B) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1136 A B t s h _76272 _76274 _76273) = (term1152 A B _76273 h _76274 s _76272 t).
Proof. exact (TRANS (@lem5996315 A B s t h _76272 _76274 _76273) (@lem5996437 A B _76273 h _76274 s _76272 t)). Qed.
Lemma lem5996439 {A B : Type'} (h : A -> B) (_76273 : A) (_76272 : B) : (term1143 A B h _76273 _76272) = (term1143 A B h _76273 _76272).
Proof. exact (eq_refl (term1143 A B h _76273 _76272)). Qed.
Lemma lem5996440 {A B : Type'} (_76273 : A) (h : A -> B) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1135 A B t s h _76272 _76274 _76273) = (term1153 A B _76273 h _76274 s _76272 t).
Proof. exact (MK_COMB (@lem5996439 A B h _76273 _76272) (@lem5996438 A B _76273 h _76274 s _76272 t)). Qed.
Lemma lem5996444 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5996445 {A B : Type'} (_76273 : A) (h : A -> B) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1153 A B _76273 h _76274 s _76272 t) = (term1154 A B _76273 h _76274 s _76272 t).
Proof. exact (@lem5996444 (_76274 = _76273) (term1124 A B h _76273 _76272) (term1150 A B h _76274 s _76272 t)). Qed.
Lemma lem5996487 {A B : Type'} (_76273 : A) (h : A -> B) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1135 A B t s h _76272 _76274 _76273) = (term1154 A B _76273 h _76274 s _76272 t).
Proof. exact (TRANS (@lem5996440 A B _76273 h _76274 s _76272 t) (@lem5996445 A B _76273 h _76274 s _76272 t)). Qed.
Lemma lem5996488 {A B : Type'} (_76273 : A) (h : A -> B) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1134 A B t s h _76272 _76274 _76273) = (term1154 A B _76273 h _76274 s _76272 t).
Proof. exact (TRANS (@lem5996298 A B t s h _76272 _76274 _76273) (@lem5996487 A B _76273 h _76274 s _76272 t)). Qed.
Lemma lem5996489 {A : Type'} (_76273 : A) (s : A -> Prop) : (term130 A _76273 s) = (term130 A _76273 s).
Proof. exact (eq_refl (term130 A _76273 s)). Qed.
Lemma lem5996490 {A B : Type'} (_76273 : A) (h : A -> B) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1132 A B t s h _76272 _76274 _76273) = (term1155 A B _76273 h _76274 s _76272 t).
Proof. exact (MK_COMB (@lem5996489 A _76273 s) (@lem5996488 A B _76273 h _76274 s _76272 t)). Qed.
Lemma lem5996494 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5996495 {A B : Type'} (_76273 : A) (h : A -> B) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1155 A B _76273 h _76274 s _76272 t) = (term1156 A B _76273 h _76274 s _76272 t).
Proof. exact (@lem5996494 (_76274 = _76273) (term173 A _76273 s) (term1157 A B _76273 h _76274 s _76272 t)). Qed.
Lemma lem5996511 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5996512 {A B : Type'} (_76273 : A) (h : A -> B) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1158 A B _76273 h _76274 s _76272 t) = (term1159 A B _76273 h _76274 s _76272 t).
Proof. exact (@lem5996511 (term1124 A B h _76273 _76272) (term173 A _76273 s) (term1150 A B h _76274 s _76272 t)). Qed.
Lemma lem5996528 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5996529 {A B : Type'} (h : A -> B) (_76273 : A) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1160 A B _76273 h _76274 s _76272 t) = (term1161 A B h _76273 _76274 s _76272 t).
Proof. exact (@lem5996528 (term1124 A B h _76274 _76272) (term173 A _76273 s) (term1162 A B _76274 s _76272 t)). Qed.
Lemma lem5996557 {A B : Type'} (h : A -> B) (_76273 : A) (_76272 : B) : (term1143 A B h _76273 _76272) = (term1143 A B h _76273 _76272).
Proof. exact (eq_refl (term1143 A B h _76273 _76272)). Qed.
Lemma lem5996558 {A B : Type'} (h : A -> B) (_76273 : A) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1159 A B _76273 h _76274 s _76272 t) = (term1163 A B h _76273 _76274 s _76272 t).
Proof. exact (MK_COMB (@lem5996557 A B h _76273 _76272) (@lem5996529 A B h _76273 _76274 s _76272 t)). Qed.
Lemma lem5996569 {A B : Type'} (h : A -> B) (_76273 : A) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1158 A B _76273 h _76274 s _76272 t) = (term1163 A B h _76273 _76274 s _76272 t).
Proof. exact (TRANS (@lem5996512 A B _76273 h _76274 s _76272 t) (@lem5996558 A B h _76273 _76274 s _76272 t)). Qed.
Lemma lem5996570 {A : Type'} (_76274 : A) (_76273 : A) : (term1151 A _76274 _76273) = (term1151 A _76274 _76273).
Proof. exact (eq_refl (term1151 A _76274 _76273)). Qed.
Lemma lem5996571 {A B : Type'} (h : A -> B) (_76273 : A) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1156 A B _76273 h _76274 s _76272 t) = (term1164 A B h _76273 _76274 s _76272 t).
Proof. exact (MK_COMB (@lem5996570 A _76274 _76273) (@lem5996569 A B h _76273 _76274 s _76272 t)). Qed.
Lemma lem5996582 {A B : Type'} (h : A -> B) (_76273 : A) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1155 A B _76273 h _76274 s _76272 t) = (term1164 A B h _76273 _76274 s _76272 t).
Proof. exact (TRANS (@lem5996495 A B _76273 h _76274 s _76272 t) (@lem5996571 A B h _76273 _76274 s _76272 t)). Qed.
Lemma lem5996583 {A B : Type'} (h : A -> B) (_76273 : A) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1132 A B t s h _76272 _76274 _76273) = (term1164 A B h _76273 _76274 s _76272 t).
Proof. exact (TRANS (@lem5996490 A B _76273 h _76274 s _76272 t) (@lem5996582 A B h _76273 _76274 s _76272 t)). Qed.
Lemma lem5996584 {A B : Type'} (h : A -> B) (_76273 : A) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1127 A B t s h _76272 _76274 _76273) = (term1164 A B h _76273 _76274 s _76272 t).
Proof. exact (TRANS (@lem5996283 A B t s h _76272 _76274 _76273) (@lem5996583 A B h _76273 _76274 s _76272 t)). Qed.
Lemma lem5996585 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5996586 {A B : Type'} (h : A -> B) (_76273 : A) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1165 A B t s h _76272 _76274 _76273) = (term1166 A B h _76273 _76274 s _76272 t).
Proof. exact (MK_COMB (@lem5996585) (@lem5996584 A B h _76273 _76274 s _76272 t)). Qed.
Lemma lem5996602 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5996603 {A B : Type'} (t : B -> Prop) (_76273 : A) (s : A -> Prop) (h : A -> B) (_76274 : A) (_76272 : B) : (term1167 A B t _76273 s h _76274 _76272) = (term1168 A B t _76273 s h _76274 _76272).
Proof. exact (@lem5996602 (term173 A _76273 s) (term173 B _76272 t) (term1169 A B _76273 s h _76274 _76272)). Qed.
Lemma lem5996617 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5996618 {A B : Type'} (_76273 : A) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (_76274 : A) (_76272 : B) : (term1170 A B t _76273 s h _76274 _76272) = (term1171 A B _76273 t s h _76274 _76272).
Proof. exact (@lem5996617 (term1124 A B h _76273 _76272) (term173 B _76272 t) (term105 A B s h _76274 _76272)). Qed.
Lemma lem5996634 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5996635 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h : A -> B) (_76274 : A) (_76272 : B) : (term1172 A B t s h _76274 _76272) = (term1173 A B s t h _76274 _76272).
Proof. exact (@lem5996634 (term173 A _76274 s) (term173 B _76272 t) (term1124 A B h _76274 _76272)). Qed.
Lemma lem5996649 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5996650 {A B : Type'} (h : A -> B) (_76274 : A) (_76272 : B) (t : B -> Prop) : (term1174 A B t h _76274 _76272) = (term1148 A B h _76274 _76272 t).
Proof. exact (@lem5996649 (term1124 A B h _76274 _76272) (term173 B _76272 t)). Qed.
Lemma lem5996658 {A : Type'} (_76274 : A) (s : A -> Prop) : (term130 A _76274 s) = (term130 A _76274 s).
Proof. exact (eq_refl (term130 A _76274 s)). Qed.
Lemma lem5996659 {A B : Type'} (s : A -> Prop) (h : A -> B) (_76274 : A) (_76272 : B) (t : B -> Prop) : (term1173 A B s t h _76274 _76272) = (term1149 A B s h _76274 _76272 t).
Proof. exact (MK_COMB (@lem5996658 A _76274 s) (@lem5996650 A B h _76274 _76272 t)). Qed.
Lemma lem5996663 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5996664 {A B : Type'} (h : A -> B) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1149 A B s h _76274 _76272 t) = (term1150 A B h _76274 s _76272 t).
Proof. exact (@lem5996663 (term1124 A B h _76274 _76272) (term173 A _76274 s) (term173 B _76272 t)). Qed.
Lemma lem5996682 {A B : Type'} (h : A -> B) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1173 A B s t h _76274 _76272) = (term1150 A B h _76274 s _76272 t).
Proof. exact (TRANS (@lem5996659 A B s h _76274 _76272 t) (@lem5996664 A B h _76274 s _76272 t)). Qed.
Lemma lem5996683 {A B : Type'} (h : A -> B) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1172 A B t s h _76274 _76272) = (term1150 A B h _76274 s _76272 t).
Proof. exact (TRANS (@lem5996635 A B s t h _76274 _76272) (@lem5996682 A B h _76274 s _76272 t)). Qed.
Lemma lem5996684 {A B : Type'} (h : A -> B) (_76273 : A) (_76272 : B) : (term1143 A B h _76273 _76272) = (term1143 A B h _76273 _76272).
Proof. exact (eq_refl (term1143 A B h _76273 _76272)). Qed.
Lemma lem5996685 {A B : Type'} (_76273 : A) (h : A -> B) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1171 A B _76273 t s h _76274 _76272) = (term1157 A B _76273 h _76274 s _76272 t).
Proof. exact (MK_COMB (@lem5996684 A B h _76273 _76272) (@lem5996683 A B h _76274 s _76272 t)). Qed.
Lemma lem5996696 {A B : Type'} (_76273 : A) (h : A -> B) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1170 A B t _76273 s h _76274 _76272) = (term1157 A B _76273 h _76274 s _76272 t).
Proof. exact (TRANS (@lem5996618 A B _76273 t s h _76274 _76272) (@lem5996685 A B _76273 h _76274 s _76272 t)). Qed.
Lemma lem5996697 {A : Type'} (_76273 : A) (s : A -> Prop) : (term130 A _76273 s) = (term130 A _76273 s).
Proof. exact (eq_refl (term130 A _76273 s)). Qed.
Lemma lem5996698 {A B : Type'} (_76273 : A) (h : A -> B) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1168 A B t _76273 s h _76274 _76272) = (term1158 A B _76273 h _76274 s _76272 t).
Proof. exact (MK_COMB (@lem5996697 A _76273 s) (@lem5996696 A B _76273 h _76274 s _76272 t)). Qed.
Lemma lem5996702 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5996703 {A B : Type'} (_76273 : A) (h : A -> B) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1158 A B _76273 h _76274 s _76272 t) = (term1159 A B _76273 h _76274 s _76272 t).
Proof. exact (@lem5996702 (term1124 A B h _76273 _76272) (term173 A _76273 s) (term1150 A B h _76274 s _76272 t)). Qed.
Lemma lem5996719 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5996720 {A B : Type'} (h : A -> B) (_76273 : A) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1160 A B _76273 h _76274 s _76272 t) = (term1161 A B h _76273 _76274 s _76272 t).
Proof. exact (@lem5996719 (term1124 A B h _76274 _76272) (term173 A _76273 s) (term1162 A B _76274 s _76272 t)). Qed.
Lemma lem5996748 {A B : Type'} (h : A -> B) (_76273 : A) (_76272 : B) : (term1143 A B h _76273 _76272) = (term1143 A B h _76273 _76272).
Proof. exact (eq_refl (term1143 A B h _76273 _76272)). Qed.
Lemma lem5996749 {A B : Type'} (h : A -> B) (_76273 : A) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1159 A B _76273 h _76274 s _76272 t) = (term1163 A B h _76273 _76274 s _76272 t).
Proof. exact (MK_COMB (@lem5996748 A B h _76273 _76272) (@lem5996720 A B h _76273 _76274 s _76272 t)). Qed.
Lemma lem5996760 {A B : Type'} (h : A -> B) (_76273 : A) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1158 A B _76273 h _76274 s _76272 t) = (term1163 A B h _76273 _76274 s _76272 t).
Proof. exact (TRANS (@lem5996703 A B _76273 h _76274 s _76272 t) (@lem5996749 A B h _76273 _76274 s _76272 t)). Qed.
Lemma lem5996761 {A B : Type'} (h : A -> B) (_76273 : A) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1168 A B t _76273 s h _76274 _76272) = (term1163 A B h _76273 _76274 s _76272 t).
Proof. exact (TRANS (@lem5996698 A B _76273 h _76274 s _76272 t) (@lem5996760 A B h _76273 _76274 s _76272 t)). Qed.
Lemma lem5996762 {A B : Type'} (h : A -> B) (_76273 : A) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1167 A B t _76273 s h _76274 _76272) = (term1163 A B h _76273 _76274 s _76272 t).
Proof. exact (TRANS (@lem5996603 A B t _76273 s h _76274 _76272) (@lem5996761 A B h _76273 _76274 s _76272 t)). Qed.
Lemma lem5996763 {A : Type'} (_76274 : A) (_76273 : A) : (term1151 A _76274 _76273) = (term1151 A _76274 _76273).
Proof. exact (eq_refl (term1151 A _76274 _76273)). Qed.
Lemma lem5996764 {A B : Type'} (h : A -> B) (_76273 : A) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : (term1175 A B t _76273 s h _76274 _76272) = (term1164 A B h _76273 _76274 s _76272 t).
Proof. exact (MK_COMB (@lem5996763 A _76274 _76273) (@lem5996762 A B h _76273 _76274 s _76272 t)). Qed.
Lemma lem5996775 {A B : Type'} (h : A -> B) (_76273 : A) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : ((term1127 A B t s h _76272 _76274 _76273) = (term1175 A B t _76273 s h _76274 _76272)) = ((term1164 A B h _76273 _76274 s _76272 t) = (term1164 A B h _76273 _76274 s _76272 t)).
Proof. exact (MK_COMB (@lem5996586 A B h _76273 _76274 s _76272 t) (@lem5996764 A B h _76273 _76274 s _76272 t)). Qed.
Lemma lem5996777 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5996778 (x : Prop) : (x = x) = True.
Proof. exact (@lem5996777 Prop x). Qed.
Lemma lem5996779 {A B : Type'} (h : A -> B) (_76273 : A) (_76274 : A) (s : A -> Prop) (_76272 : B) (t : B -> Prop) : ((term1164 A B h _76273 _76274 s _76272 t) = (term1164 A B h _76273 _76274 s _76272 t)) = True.
Proof. exact (@lem5996778 (term1164 A B h _76273 _76274 s _76272 t)). Qed.
Lemma lem5996780 {A B : Type'} (t : B -> Prop) (_76273 : A) (s : A -> Prop) (h : A -> B) (_76274 : A) (_76272 : B) : ((term1127 A B t s h _76272 _76274 _76273) = (term1175 A B t _76273 s h _76274 _76272)) = True.
Proof. exact (TRANS (@lem5996775 A B h _76273 _76274 s _76272 t) (@lem5996779 A B h _76273 _76274 s _76272 t)). Qed.
Lemma lem5996781 {A B : Type'} (t : B -> Prop) (_76273 : A) (s : A -> Prop) (h : A -> B) (_76274 : A) (_76272 : B) : True = ((term1127 A B t s h _76272 _76274 _76273) = (term1175 A B t _76273 s h _76274 _76272)).
Proof. exact (SYM (@lem5996780 A B t _76273 s h _76274 _76272)). Qed.
Lemma lem5996782 {A B : Type'} (t : B -> Prop) (_76273 : A) (s : A -> Prop) (h : A -> B) (_76274 : A) (_76272 : B) : (term1127 A B t s h _76272 _76274 _76273) = (term1175 A B t _76273 s h _76274 _76272).
Proof. exact (EQ_MP (@lem5996781 A B t _76273 s h _76274 _76272) (@lem0)). Qed.
Lemma lem5996783 {A B : Type'} (_76273 : A) (_76274 : A) (_76272 : B) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x' s h) : term1175 A B t _76273 s h _76274 _76272.
Proof. exact (EQ_MP (@lem5996782 A B t _76273 s h _76274 _76272) (@lem5996082 A B _76272 _76274 _76273 t x' s h h1)). Qed.
Lemma lem5996785 (b : Prop) (a : Prop) : (a \/ b) = (term364 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5996786 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (_76272 : B) (_76274 : A) (_76273 : A) : (term1175 A B t _76273 s h _76274 _76272) = (term1176 A B t s h _76272 _76274 _76273).
Proof. exact (@lem5996785 (term1167 A B t _76273 s h _76274 _76272) (_76274 = _76273)). Qed.
Lemma lem5996788 (a : Prop) (b : Prop) : (term383 a b) = (term384 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5996789 {A B : Type'} (t : B -> Prop) (_76273 : A) (s : A -> Prop) (h : A -> B) (_76274 : A) (_76272 : B) : (term1177 A B t _76273 s h _76274 _76272) = (term1178 A B t _76273 s h _76274 _76272).
Proof. exact (@lem5996788 (term173 B _76272 t) (term1179 A B _76273 s h _76274 _76272)). Qed.
Lemma lem5996791 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5996792 {B : Type'} (_76272 : B) (t : B -> Prop) : (term366 B _76272 t) = (@IN B _76272 t).
Proof. exact (@lem5996791 (@IN B _76272 t)). Qed.
Lemma lem5996793 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5996794 {B : Type'} (_76272 : B) (t : B -> Prop) : (term1180 B _76272 t) = (term228 B _76272 t).
Proof. exact (MK_COMB (@lem5996793) (@lem5996792 B _76272 t)). Qed.
Lemma lem5996796 (a : Prop) (b : Prop) : (term383 a b) = (term384 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5996797 {A B : Type'} (_76273 : A) (s : A -> Prop) (h : A -> B) (_76274 : A) (_76272 : B) : (term1181 A B _76273 s h _76274 _76272) = (term1182 A B _76273 s h _76274 _76272).
Proof. exact (@lem5996796 (term173 A _76273 s) (term1169 A B _76273 s h _76274 _76272)). Qed.
Lemma lem5996799 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5996800 {A : Type'} (_76273 : A) (s : A -> Prop) : (term366 A _76273 s) = (@IN A _76273 s).
Proof. exact (@lem5996799 (@IN A _76273 s)). Qed.
Lemma lem5996801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5996802 {A : Type'} (_76273 : A) (s : A -> Prop) : (term1180 A _76273 s) = (term228 A _76273 s).
Proof. exact (MK_COMB (@lem5996801) (@lem5996800 A _76273 s)). Qed.
Lemma lem5996804 (a : Prop) (b : Prop) : (term383 a b) = (term384 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5996805 {A B : Type'} (_76273 : A) (s : A -> Prop) (h : A -> B) (_76274 : A) (_76272 : B) : (term1183 A B _76273 s h _76274 _76272) = (term1184 A B _76273 s h _76274 _76272).
Proof. exact (@lem5996804 (term1124 A B h _76273 _76272) (term105 A B s h _76274 _76272)). Qed.
Lemma lem5996807 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5996808 {A B : Type'} (h : A -> B) (_76273 : A) (_76272 : B) : (term1185 A B h _76273 _76272) = ((h _76273) = _76272).
Proof. exact (@lem5996807 ((h _76273) = _76272)). Qed.
Lemma lem5996809 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5996810 {A B : Type'} (h : A -> B) (_76273 : A) (_76272 : B) : (term1186 A B h _76273 _76272) = (term1187 A B h _76273 _76272).
Proof. exact (MK_COMB (@lem5996809) (@lem5996808 A B h _76273 _76272)). Qed.
Lemma lem5996812 (a : Prop) (b : Prop) : (term383 a b) = (term384 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5996813 {A B : Type'} (s : A -> Prop) (h : A -> B) (_76274 : A) (_76272 : B) : (term1188 A B s h _76274 _76272) = (term1189 A B s h _76274 _76272).
Proof. exact (@lem5996812 (term173 A _76274 s) (term1124 A B h _76274 _76272)). Qed.
Lemma lem5996815 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5996816 {A : Type'} (_76274 : A) (s : A -> Prop) : (term366 A _76274 s) = (@IN A _76274 s).
Proof. exact (@lem5996815 (@IN A _76274 s)). Qed.
Lemma lem5996817 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5996818 {A : Type'} (_76274 : A) (s : A -> Prop) : (term1180 A _76274 s) = (term228 A _76274 s).
Proof. exact (MK_COMB (@lem5996817) (@lem5996816 A _76274 s)). Qed.
Lemma lem5996820 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5996821 {A B : Type'} (h : A -> B) (_76274 : A) (_76272 : B) : (term1185 A B h _76274 _76272) = ((h _76274) = _76272).
Proof. exact (@lem5996820 ((h _76274) = _76272)). Qed.
Lemma lem5996822 {A B : Type'} (s : A -> Prop) (h : A -> B) (_76274 : A) (_76272 : B) : (term1189 A B s h _76274 _76272) = (term96 A B s h _76274 _76272).
Proof. exact (MK_COMB (@lem5996818 A _76274 s) (@lem5996821 A B h _76274 _76272)). Qed.
Lemma lem5996823 {A B : Type'} (s : A -> Prop) (h : A -> B) (_76274 : A) (_76272 : B) : (term1188 A B s h _76274 _76272) = (term96 A B s h _76274 _76272).
Proof. exact (TRANS (@lem5996813 A B s h _76274 _76272) (@lem5996822 A B s h _76274 _76272)). Qed.
Lemma lem5996824 {A B : Type'} (_76273 : A) (s : A -> Prop) (h : A -> B) (_76274 : A) (_76272 : B) : (term1184 A B _76273 s h _76274 _76272) = (term1190 A B _76273 s h _76274 _76272).
Proof. exact (MK_COMB (@lem5996810 A B h _76273 _76272) (@lem5996823 A B s h _76274 _76272)). Qed.
Lemma lem5996825 {A B : Type'} (_76273 : A) (s : A -> Prop) (h : A -> B) (_76274 : A) (_76272 : B) : (term1183 A B _76273 s h _76274 _76272) = (term1190 A B _76273 s h _76274 _76272).
Proof. exact (TRANS (@lem5996805 A B _76273 s h _76274 _76272) (@lem5996824 A B _76273 s h _76274 _76272)). Qed.
Lemma lem5996826 {A B : Type'} (_76273 : A) (s : A -> Prop) (h : A -> B) (_76274 : A) (_76272 : B) : (term1182 A B _76273 s h _76274 _76272) = (term1191 A B _76273 s h _76274 _76272).
Proof. exact (MK_COMB (@lem5996802 A _76273 s) (@lem5996825 A B _76273 s h _76274 _76272)). Qed.
Lemma lem5996827 {A B : Type'} (_76273 : A) (s : A -> Prop) (h : A -> B) (_76274 : A) (_76272 : B) : (term1181 A B _76273 s h _76274 _76272) = (term1191 A B _76273 s h _76274 _76272).
Proof. exact (TRANS (@lem5996797 A B _76273 s h _76274 _76272) (@lem5996826 A B _76273 s h _76274 _76272)). Qed.
Lemma lem5996828 {A B : Type'} (t : B -> Prop) (_76273 : A) (s : A -> Prop) (h : A -> B) (_76274 : A) (_76272 : B) : (term1178 A B t _76273 s h _76274 _76272) = (term1192 A B t _76273 s h _76274 _76272).
Proof. exact (MK_COMB (@lem5996794 B _76272 t) (@lem5996827 A B _76273 s h _76274 _76272)). Qed.
Lemma lem5996829 {A B : Type'} (t : B -> Prop) (_76273 : A) (s : A -> Prop) (h : A -> B) (_76274 : A) (_76272 : B) : (term1177 A B t _76273 s h _76274 _76272) = (term1192 A B t _76273 s h _76274 _76272).
Proof. exact (TRANS (@lem5996789 A B t _76273 s h _76274 _76272) (@lem5996828 A B t _76273 s h _76274 _76272)). Qed.
Lemma lem5996830 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5996831 {A B : Type'} (t : B -> Prop) (_76273 : A) (s : A -> Prop) (h : A -> B) (_76274 : A) (_76272 : B) : (term1193 A B t _76273 s h _76274 _76272) = (term1194 A B t _76273 s h _76274 _76272).
Proof. exact (MK_COMB (@lem5996830) (@lem5996829 A B t _76273 s h _76274 _76272)). Qed.
Lemma lem5996832 {A : Type'} (_76274 : A) (_76273 : A) : (_76274 = _76273) = (_76274 = _76273).
Proof. exact (eq_refl (_76274 = _76273)). Qed.
Lemma lem5996833 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (_76272 : B) (_76274 : A) (_76273 : A) : (term1176 A B t s h _76272 _76274 _76273) = (term1195 A B t s h _76272 _76274 _76273).
Proof. exact (MK_COMB (@lem5996831 A B t _76273 s h _76274 _76272) (@lem5996832 A _76274 _76273)). Qed.
Lemma lem5996834 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h : A -> B) (_76272 : B) (_76274 : A) (_76273 : A) : (term1175 A B t _76273 s h _76274 _76272) = (term1195 A B t s h _76272 _76274 _76273).
Proof. exact (TRANS (@lem5996786 A B t s h _76272 _76274 _76273) (@lem5996833 A B t s h _76272 _76274 _76273)). Qed.
Lemma lem5996836 {A B : Type'} (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term1121 A B s x h y) : term1196 A B s x h y.
Proof. exact (conj (@lem5996269 A B s x h y h1) (@lem5996276 A B s x h y h1)). Qed.
Lemma lem5996837 {A B : Type'} (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term1121 A B s x h y) : term1197 A B s x h y.
Proof. exact (conj (@lem5996262 A B h y) (@lem5996836 A B s x h y h1)). Qed.
Lemma lem5996838 {A B : Type'} (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term1121 A B s x h y) : term1198 A B s x h y.
Proof. exact (conj (@lem5996253 A B s x h y h1) (@lem5996837 A B s x h y h1)). Qed.
Lemma lem5996839 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> C) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term1121 A B s x h y) : term1199 A B t s x h y.
Proof. exact (conj (@lem5996246 A B C t g f s x h y h1 h2) (@lem5996838 A B s x h y h2)). Qed.
Lemma lem5996841 {A B : Type'} (_76272 : B) (_76274 : A) (_76273 : A) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x' s h) : term1195 A B t s h _76272 _76274 _76273.
Proof. exact (EQ_MP (@lem5996834 A B t s h _76272 _76274 _76273) (@lem5996783 A B _76273 _76274 _76272 t x' s h h1)). Qed.
Lemma lem5996842 {A B : Type'} (_76272 : B) (_76274 : A) (_76273 : A) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x' s h) : term1195 A B t s h _76272 _76274 _76273.
Proof. exact (@lem5996841 A B _76272 _76274 _76273 t x' s h h1). Qed.
Lemma lem5996843 {A B : Type'} (x : A) (y : A) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (h : A -> B) (h1 : term207 A B t x' s h) : term1200 A B t s h x y.
Proof. exact (@lem5996842 A B (h y) x y t x' s h h1). Qed.
Lemma lem5996846 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term207 A B t x' s h) (h3 : term1121 A B s x h y) : x = y.
Proof. exact (@lem5996843 A B x y t x' s h h2 (@lem5996839 A B C t g f s x h y h1 h3)). Qed.
Lemma lem5996847 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term207 A B t x' s h) (h3 : term1121 A B s x h y) : term1201 A x y.
Proof. exact (fun h0 : term375 A x y => @lem5996846 A B C g f t x' s x h y h1 h2 h3). Qed.
Lemma lem5996849 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5996850 {A : Type'} (x : A) (y : A) : (term1201 A x y) = (x = y).
Proof. exact (@lem5996849 (x = y)). Qed.
Lemma lem5996851 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term207 A B t x' s h) (h3 : term1121 A B s x h y) : x = y.
Proof. exact (EQ_MP (@lem5996850 A x y) (@lem5996847 A B C g f t x' s x h y h1 h2 h3)). Qed.
Lemma lem5996854 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5996856 {A : Type'} (x : A) (y : A) : (term375 A x y) = (term1202 A x y).
Proof. exact (@lem5996854 (x = y)). Qed.
Lemma lem5996859 {A : Type'} (x : A) (y : A) (h1 : term375 A x y) : term1202 A x y.
Proof. exact (EQ_MP (@lem5996856 A x y) (@lem5996050 A x y h1)). Qed.
Lemma lem5996862 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term207 A B t x' s h) (h3 : term375 A x y) (h4 : term1121 A B s x h y) : False.
Proof. exact (@lem5996859 A x y h3 (@lem5996851 A B C g f t x' s x h y h1 h2 h4)). Qed.
Lemma lem5996863 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term207 A B t x' s h) (h3 : term375 A x y) (h4 : term1121 A B s x h y) : term410.
Proof. exact (fun h0 : ~ False => @lem5996862 A B C g f t x' s x h y h1 h2 h3 h4). Qed.
Lemma lem5996865 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5996866 : term410 = False.
Proof. exact (@lem5996865 False). Qed.
Lemma lem5996867 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term207 A B t x' s h) (h3 : term375 A x y) (h4 : term1121 A B s x h y) : False.
Proof. exact (EQ_MP (@lem5996866) (@lem5996863 A B C g f t x' s x h y h1 h2 h3 h4)). Qed.
Lemma lem5996868 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term207 A B t x' s h) (h3 : term375 A x y) (h4 : term1121 A B s x h y) : (term375 A x y) = False.
Proof. exact (prop_ext (fun h5 : term375 A x y => @lem5996867 A B C g f t x' s x h y h1 h2 h3 h4) (fun h5 : False => @lem5996050 A x y h3)). Qed.
Lemma lem5996869 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term207 A B t x' s h) (h3 : term375 A x y) (h4 : term1121 A B s x h y) : False.
Proof. exact (EQ_MP (@lem5996868 A B C g f t x' s x h y h1 h2 h3 h4) (@lem5996050 A x y h3)). Qed.
Lemma lem5996870 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term207 A B t x' s h) (h3 : term375 A x y) (h4 : term1121 A B s x h y) : (term375 A x y) = False.
Proof. exact (prop_ext (fun h5 : term375 A x y => @lem5996869 A B C g f t x' s x h y h1 h2 h3 h4) (fun h5 : False => @lem5995836 A x y h3)). Qed.
Lemma lem5996871 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term207 A B t x' s h) (h3 : term375 A x y) (h4 : term1121 A B s x h y) : False.
Proof. exact (EQ_MP (@lem5996870 A B C g f t x' s x h y h1 h2 h3 h4) (@lem5995836 A x y h3)). Qed.
Lemma lem5996872 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term207 A B t x' s h) (h3 : term375 A x y) (h4 : term1121 A B s x h y) : (term375 A x y) = False.
Proof. exact (prop_ext (fun h5 : term375 A x y => @lem5996871 A B C g f t x' s x h y h1 h2 h3 h4) (fun h5 : False => @lem5995836 A x y h3)). Qed.
Lemma lem5996873 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term207 A B t x' s h) (h3 : term375 A x y) (h4 : term1121 A B s x h y) : False.
Proof. exact (EQ_MP (@lem5996872 A B C g f t x' s x h y h1 h2 h3 h4) (@lem5995836 A x y h3)). Qed.
Lemma lem5996874 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term207 A B t x' s h) (h3 : term375 A x y) (h4 : term1121 A B s x h y) : (term207 A B t x' s h) = False.
Proof. exact (prop_ext (fun h5 : term207 A B t x' s h => @lem5996873 A B C g f t x' s x h y h1 h2 h3 h4) (fun h5 : False => @lem5995805 A B t x' s h h2)). Qed.
Lemma lem5996875 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term207 A B t x' s h) (h3 : term375 A x y) (h4 : term1121 A B s x h y) : False.
Proof. exact (EQ_MP (@lem5996874 A B C g f t x' s x h y h1 h2 h3 h4) (@lem5995805 A B t x' s h h2)). Qed.
Lemma lem5996876 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term207 A B t x' s h) (h3 : term375 A x y) (h4 : term1121 A B s x h y) : (term375 A x y) = False.
Proof. exact (prop_ext (fun h5 : term375 A x y => @lem5996875 A B C g f t x' s x h y h1 h2 h3 h4) (fun h5 : False => @lem5995714 A x y h3)). Qed.
Lemma lem5996877 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term207 A B t x' s h) (h3 : term375 A x y) (h4 : term1121 A B s x h y) : False.
Proof. exact (EQ_MP (@lem5996876 A B C g f t x' s x h y h1 h2 h3 h4) (@lem5995714 A x y h3)). Qed.
Lemma lem5996878 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term207 A B t x' s h) (h3 : term375 A x y) (h4 : term1121 A B s x h y) : (term1121 A B s x h y) = False.
Proof. exact (prop_ext (fun h5 : term1121 A B s x h y => @lem5996877 A B C g f t x' s x h y h1 h2 h3 h4) (fun h5 : False => @lem5995706 A B s x h y h4)). Qed.
Lemma lem5996879 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term207 A B t x' s h) (h3 : term375 A x y) (h4 : term1121 A B s x h y) : False.
Proof. exact (EQ_MP (@lem5996878 A B C g f t x' s x h y h1 h2 h3 h4) (@lem5995706 A B s x h y h4)). Qed.
Lemma lem5996880 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term375 A x y) (h4 : term1121 A B s x h y) : False.
Proof. exact (ex_elim (@lem5995557 A B t s h h2) (fun x' : B -> A => fun h0 : term209 A B t s h x' => @lem5996879 A B C g f t x' s x h y h1 h0 h3 h4)). Qed.
Lemma lem5996881 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term375 A x y) (h4 : term1121 A B s x h y) : (term375 A x y) = False.
Proof. exact (prop_ext (fun h5 : term375 A x y => @lem5996880 A B C g f t s x h y h1 h2 h3 h4) (fun h5 : False => @lem5995644 A x y h3)). Qed.
Lemma lem5996882 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term375 A x y) (h4 : term1121 A B s x h y) : False.
Proof. exact (EQ_MP (@lem5996881 A B C g f t s x h y h1 h2 h3 h4) (@lem5995644 A x y h3)). Qed.
Lemma lem5996883 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term375 A x y) (h4 : term1121 A B s x h y) : (term1121 A B s x h y) = False.
Proof. exact (prop_ext (fun h5 : term1121 A B s x h y => @lem5996882 A B C g f t s x h y h1 h2 h3 h4) (fun h5 : False => @lem5995638 A B s x h y h4)). Qed.
Lemma lem5996884 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term375 A x y) (h4 : term1121 A B s x h y) : False.
Proof. exact (EQ_MP (@lem5996883 A B C g f t s x h y h1 h2 h3 h4) (@lem5995638 A B s x h y h4)). Qed.
Lemma lem5996885 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term375 A x y) (h4 : term1121 A B s x h y) : (term375 A x y) = False.
Proof. exact (prop_ext (fun h5 : term375 A x y => @lem5996884 A B C g f t s x h y h1 h2 h3 h4) (fun h5 : False => @lem5995145 A x y h3)). Qed.
Lemma lem5996886 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term375 A x y) (h4 : term1121 A B s x h y) : False.
Proof. exact (EQ_MP (@lem5996885 A B C g f t s x h y h1 h2 h3 h4) (@lem5995145 A x y h3)). Qed.
Lemma lem5996887 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term1121 A B s x h y) : term1120 A x y.
Proof. exact (fun h0 : term375 A x y => @lem5996886 A B C g f t s x h y h1 h2 h0 h3). Qed.
Lemma lem5996888 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (x : A) (h : A -> B) (y : A) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term1121 A B s x h y) : x = y.
Proof. exact (EQ_MP (@lem5995144 A x y) (@lem5996887 A B C g f t s x h y h1 h2 h3)). Qed.
Lemma lem5996889 {A B C : Type'} (x : A) (y : A) (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) : term1116 A B s h x y.
Proof. exact (fun h0 : term1121 A B s x h y => @lem5996888 A B C g f t s x h y h1 h2 h0). Qed.
Lemma lem5996894 {A B C : Type'} (x : A) (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) : term1118 A B s h x.
Proof. exact (fun y : A => @lem5996889 A B C x y g f t s h h1 h2). Qed.
Lemma lem5996899 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) : term1077 A B s h.
Proof. exact (fun x : A => @lem5996894 A B C x g f t s h h1 h2). Qed.
Lemma lem5996900 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (h1 : term39 A B t s h) : term1094 A B C t g f s h.
Proof. exact (fun h0 : term38 A B C s t g h f => @lem5996899 A B C g f t s h h0 h1). Qed.
Lemma lem5996901 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) : term1095 A B C t g f s h.
Proof. exact (fun h0 : term39 A B t s h => @lem5996900 A B C g f t s h h0). Qed.
Lemma lem5996906 {A B C : Type'} (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) : term1099 A B C g f s h.
Proof. exact (fun t : B -> Prop => @lem5996901 A B C t g f s h). Qed.
Lemma lem5996911 {A B C : Type'} (f : A -> C) (s : A -> Prop) (h : A -> B) : term1103 A B C f s h.
Proof. exact (fun g : B -> C => @lem5996906 A B C g f s h). Qed.
Lemma lem5996916 {A B C : Type'} (s : A -> Prop) (h : A -> B) : term1107 A B C s h.
Proof. exact (fun f : A -> C => @lem5996911 A B C f s h). Qed.
Lemma lem5996921 {A B C : Type'} (h : A -> B) : term1111 A B C h.
Proof. exact (fun s : A -> Prop => @lem5996916 A B C s h). Qed.
Lemma lem5996926 {A B C : Type'} : term1115 A B C.
Proof. exact (fun h : A -> B => @lem5996921 A B C h). Qed.
Lemma lem5996927 {A B C : Type'} : term1114 A B C.
Proof. exact (EQ_MP (@lem5995137 A B C) (@lem5996926 A B C)). Qed.
Lemma lem5996928 {A B C : Type'} (h : A -> B) : term1203 A B C h.
Proof. exact (@lem5996927 A B C h). Qed.
Lemma lem5996929 {A B C : Type'} (h : A -> B) : (term1203 A B C h) = (term1110 A B C h).
Proof. exact (eq_refl (term1203 A B C h)). Qed.
Lemma lem5996930 {A B C : Type'} (h : A -> B) : term1110 A B C h.
Proof. exact (EQ_MP (@lem5996929 A B C h) (@lem5996928 A B C h)). Qed.
Lemma lem5996931 {A B C : Type'} (h : A -> B) (s : A -> Prop) : term1204 A B C h s.
Proof. exact (@lem5996930 A B C h s). Qed.
Lemma lem5996932 {A B C : Type'} (s : A -> Prop) (h : A -> B) : (term1204 A B C h s) = (term1106 A B C s h).
Proof. exact (eq_refl (term1204 A B C h s)). Qed.
Lemma lem5996933 {A B C : Type'} (s : A -> Prop) (h : A -> B) : term1106 A B C s h.
Proof. exact (EQ_MP (@lem5996932 A B C s h) (@lem5996931 A B C h s)). Qed.
Lemma lem5996934 {A B C : Type'} (s : A -> Prop) (h : A -> B) (f : A -> C) : term1205 A B C s h f.
Proof. exact (@lem5996933 A B C s h f). Qed.
Lemma lem5996935 {A B C : Type'} (f : A -> C) (s : A -> Prop) (h : A -> B) : (term1205 A B C s h f) = (term1102 A B C f s h).
Proof. exact (eq_refl (term1205 A B C s h f)). Qed.
Lemma lem5996936 {A B C : Type'} (f : A -> C) (s : A -> Prop) (h : A -> B) : term1102 A B C f s h.
Proof. exact (EQ_MP (@lem5996935 A B C f s h) (@lem5996934 A B C s h f)). Qed.
Lemma lem5996937 {A B C : Type'} (f : A -> C) (s : A -> Prop) (h : A -> B) (g : B -> C) : term1206 A B C f s h g.
Proof. exact (@lem5996936 A B C f s h g). Qed.
Lemma lem5996938 {A B C : Type'} (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) : (term1206 A B C f s h g) = (term1098 A B C g f s h).
Proof. exact (eq_refl (term1206 A B C f s h g)). Qed.
Lemma lem5996939 {A B C : Type'} (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) : term1098 A B C g f s h.
Proof. exact (EQ_MP (@lem5996938 A B C g f s h) (@lem5996937 A B C f s h g)). Qed.
Lemma lem5996940 {A B C : Type'} (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) (t : B -> Prop) : term1207 A B C g f s h t.
Proof. exact (@lem5996939 A B C g f s h t). Qed.
Lemma lem5996941 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) : (term1207 A B C g f s h t) = (term1088 A B C t g f s h).
Proof. exact (eq_refl (term1207 A B C g f s h t)). Qed.
Lemma lem5996942 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) : term1088 A B C t g f s h.
Proof. exact (EQ_MP (@lem5996941 A B C t g f s h) (@lem5996940 A B C g f s h t)). Qed.
Lemma lem5996944 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> C) (s : A -> Prop) (h : A -> B) : term1088 A B C t g f s h.
Proof. exact (@lem5994886 A B C t g f s h (@lem5996942 A B C t g f s h)). Qed.
Lemma lem5996945 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (h1 : term39 A B t s h) : term1093 A B C t g f s h.
Proof. exact (@lem5996944 A B C t g f s h (@lem5986689 A B t s h h1)). Qed.
Lemma lem5996946 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) : term1086 A B s h.
Proof. exact (@lem5996945 A B C g f t s h h2 (@lem5986688 A B C s t g h f h1)). Qed.
Lemma lem5996947 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term1087 A B s h) : False.
Proof. exact (@lem5996946 A B C g f t s h h1 h2 (@lem5994870 A B s h h3)). Qed.
Lemma lem5996948 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term1087 A B s h) : (term1087 A B s h) = False.
Proof. exact (prop_ext (fun h4 : term1087 A B s h => @lem5996947 A B C g f t s h h1 h2 h3) (fun h4 : False => @lem5994870 A B s h h3)). Qed.
Lemma lem5996949 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : term1087 A B s h) : False.
Proof. exact (EQ_MP (@lem5996948 A B C g f t s h h1 h2 h3) (@lem5994870 A B s h h3)). Qed.
Lemma lem5996950 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) : term1086 A B s h.
Proof. exact (fun h0 : term1087 A B s h => @lem5996949 A B C g f t s h h1 h2 h0). Qed.
Lemma lem5996951 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) : term1077 A B s h.
Proof. exact (EQ_MP (@lem5994869 A B s h) (@lem5996950 A B C g f t s h h1 h2)). Qed.
Lemma lem5996952 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (op : type1400 C) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) : (term43 A B C op h s g) = (term425 A B C op s g h).
Proof. exact (@lem5994865 A B C s g h op h3 (@lem5996951 A B C g f t s h h1 h2)). Qed.
Lemma lem5996953 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (op : type1400 C) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) : (term425 A B C op s g h) = (term43 A B C op h s g).
Proof. exact (EQ_MP (@lem5994823 A B C op h s g) (@lem5996952 A B C g f t s h op h1 h2 h3)). Qed.
Lemma lem5996954 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (op : type1400 C) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) : term1208 A B C f op h s g.
Proof. exact (conj (@lem5994817 A B C g f t s h op h1 h2 h3) (@lem5996953 A B C g f t s h op h1 h2 h3)). Qed.
Lemma lem5996955 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (op : type1400 C) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) : term1209 A B C f op h s g.
Proof. exact (ex_intro (term1210 A B C f op h s g) (term425 A B C op s g h) (@lem5996954 A B C g f t s h op h1 h2 h3)). Qed.
Lemma lem5996956 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (op : type1400 C) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) : (@iterate C A op s f) = (term43 A B C op h s g).
Proof. exact (@lem5989311 A B C f op h s g (@lem5996955 A B C g f t s h op h1 h2 h3)). Qed.
Lemma lem5996957 {A B C : Type'} (g : B -> C) (f : A -> C) (op : type1400 C) (t : B -> Prop) (h : A -> B) (s : A -> Prop) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) (h4 : t = (@IMAGE A B h s)) : (@iterate C A op s f) = (@iterate C B op t g).
Proof. exact (EQ_MP (@lem5986703 A B C f op g t h s h4) (@lem5996956 A B C g f t s h op h1 h2 h3)). Qed.
Lemma lem5996958 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (op : type1400 C) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) : (t = (@IMAGE A B h s)) = ((@iterate C A op s f) = (@iterate C B op t g)).
Proof. exact (prop_ext (fun h4 : t = (@IMAGE A B h s) => @lem5996957 A B C g f op t h s h1 h2 h3 h4) (fun h4 : (@iterate C A op s f) = (@iterate C B op t g) => @lem5989307 A B C g f t s h op h1 h2 h3)). Qed.
Lemma lem5996959 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (op : type1400 C) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) : (@iterate C A op s f) = (@iterate C B op t g).
Proof. exact (EQ_MP (@lem5996958 A B C g f t s h op h1 h2 h3) (@lem5989307 A B C g f t s h op h1 h2 h3)). Qed.
Lemma lem5996960 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term37 A B C s t g h f) : term38 A B C s t g h f.
Proof. exact (proj2 (@lem5986687 A B C s t g h f h1)). Qed.
Lemma lem5996961 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term37 A B C s t g h f) : term39 A B t s h.
Proof. exact (proj1 (@lem5986687 A B C s t g h f h1)). Qed.
Lemma lem5996962 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (op : type1400 C) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) : (term38 A B C s t g h f) = ((@iterate C A op s f) = (@iterate C B op t g)).
Proof. exact (prop_ext (fun h4 : term38 A B C s t g h f => @lem5996959 A B C g f t s h op h1 h2 h3) (fun h4 : (@iterate C A op s f) = (@iterate C B op t g) => @lem5986688 A B C s t g h f h1)). Qed.
Lemma lem5996963 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (op : type1400 C) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) : (@iterate C A op s f) = (@iterate C B op t g).
Proof. exact (EQ_MP (@lem5996962 A B C g f t s h op h1 h2 h3) (@lem5986688 A B C s t g h f h1)). Qed.
Lemma lem5996964 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (op : type1400 C) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) : (term39 A B t s h) = ((@iterate C A op s f) = (@iterate C B op t g)).
Proof. exact (prop_ext (fun h4 : term39 A B t s h => @lem5996963 A B C g f t s h op h1 h2 h3) (fun h4 : (@iterate C A op s f) = (@iterate C B op t g) => @lem5986689 A B t s h h2)). Qed.
Lemma lem5996965 {A B C : Type'} (g : B -> C) (f : A -> C) (t : B -> Prop) (s : A -> Prop) (h : A -> B) (op : type1400 C) (h1 : term38 A B C s t g h f) (h2 : term39 A B t s h) (h3 : @monoidal C op) : (@iterate C A op s f) = (@iterate C B op t g).
Proof. exact (EQ_MP (@lem5996964 A B C g f t s h op h1 h2 h3) (@lem5986689 A B t s h h2)). Qed.
Lemma lem5996966 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term39 A B t s h) (h2 : @monoidal C op) (h3 : term37 A B C s t g h f) : (term38 A B C s t g h f) = ((@iterate C A op s f) = (@iterate C B op t g)).
Proof. exact (prop_ext (fun h4 : term38 A B C s t g h f => @lem5996965 A B C g f t s h op h4 h1 h2) (fun h4 : (@iterate C A op s f) = (@iterate C B op t g) => @lem5996960 A B C s t g h f h3)). Qed.
Lemma lem5996967 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : term39 A B t s h) (h2 : @monoidal C op) (h3 : term37 A B C s t g h f) : (@iterate C A op s f) = (@iterate C B op t g).
Proof. exact (EQ_MP (@lem5996966 A B C op s t g h f h1 h2 h3) (@lem5996960 A B C s t g h f h3)). Qed.
Lemma lem5996968 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : @monoidal C op) (h2 : term37 A B C s t g h f) : (term39 A B t s h) = ((@iterate C A op s f) = (@iterate C B op t g)).
Proof. exact (prop_ext (fun h3 : term39 A B t s h => @lem5996967 A B C op s t g h f h3 h1 h2) (fun h3 : (@iterate C A op s f) = (@iterate C B op t g) => @lem5996961 A B C s t g h f h2)). Qed.
Lemma lem5996969 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : B -> Prop) (g : B -> C) (h : A -> B) (f : A -> C) (h1 : @monoidal C op) (h2 : term37 A B C s t g h f) : (@iterate C A op s f) = (@iterate C B op t g).
Proof. exact (EQ_MP (@lem5996968 A B C op s t g h f h1 h2) (@lem5996961 A B C s t g h f h2)). Qed.
Lemma lem5996970 {A B C : Type'} (h : A -> B) (s : A -> Prop) (f : A -> C) (t : B -> Prop) (g : B -> C) (op : type1400 C) (h1 : @monoidal C op) : term1211 A B C h s f op t g.
Proof. exact (fun h0 : term37 A B C s t g h f => @lem5996969 A B C op s t g h f h1 h0). Qed.
Lemma lem5996975 {A B C : Type'} (s : A -> Prop) (f : A -> C) (t : B -> Prop) (g : B -> C) (op : type1400 C) (h1 : @monoidal C op) : term1212 A B C s f op t g.
Proof. exact (fun h : A -> B => @lem5996970 A B C h s f t g op h1). Qed.
Lemma lem5996980 {A B C : Type'} (s : A -> Prop) (f : A -> C) (t : B -> Prop) (op : type1400 C) (h1 : @monoidal C op) : term1213 A B C s f op t.
Proof. exact (fun g : B -> C => @lem5996975 A B C s f t g op h1). Qed.
Lemma lem5996985 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (op : type1400 C) (h1 : @monoidal C op) : term1214 A B C s op t.
Proof. exact (fun f : A -> C => @lem5996980 A B C s f t op h1). Qed.
Lemma lem5996990 {A B C : Type'} (s : A -> Prop) (op : type1400 C) (h1 : @monoidal C op) : term1215 A B C s op.
Proof. exact (fun t : B -> Prop => @lem5996985 A B C s t op h1). Qed.
Lemma lem5996995 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term1216 A B C op.
Proof. exact (fun s : A -> Prop => @lem5996990 A B C s op h1). Qed.
Lemma lem5996996 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (@monoidal C op) = (term1216 A B C op).
Proof. exact (prop_ext (fun h2 : @monoidal C op => @lem5996995 A B C op h1) (fun h2 : term1216 A B C op => @lem5986686 C op h1)). Qed.
Lemma lem5996997 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term1216 A B C op.
Proof. exact (EQ_MP (@lem5996996 A B C op h1) (@lem5986686 C op h1)). Qed.
Lemma lem5996998 {A B C : Type'} (op : type1400 C) : term1217 A B C op.
Proof. exact (fun h0 : @monoidal C op => @lem5996997 A B C op h0). Qed.
Lemma lem5997003 {A B C : Type'} : term1218 A B C.
Proof. exact (fun op : type1400 C => @lem5996998 A B C op). Qed.
