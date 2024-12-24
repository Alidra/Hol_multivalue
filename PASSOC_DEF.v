Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PASSOC_DEF_term_abbrevs.
Require Import FST_spec.
Require Import SND_spec.
Lemma lem48676 {A B C D : Type'} : (@PASSOC A B C D) = (term0 A B C D).
Proof. exact (@PASSOC_def A B C D). Qed.
Lemma lem48677 {A B C D : Type'} (_1321 : type1187 A B C D) : _1321 = _1321.
Proof. exact (eq_refl _1321). Qed.
Lemma lem48678 {A B C D : Type'} (_1321 : type1187 A B C D) : (@PASSOC A B C D _1321) = (term1 A B C D _1321).
Proof. exact (MK_COMB (@lem48676 A B C D) (@lem48677 A B C D _1321)). Qed.
Lemma lem48679 {A B C D : Type'} (_1321 : type1187 A B C D) : (term1 A B C D _1321) = (term2 A B C D _1321).
Proof. exact (eq_refl (term1 A B C D _1321)). Qed.
Lemma lem48680 {A B C D : Type'} (_1321 : type1187 A B C D) : (@PASSOC A B C D _1321) = (term2 A B C D _1321).
Proof. exact (TRANS (@lem48678 A B C D _1321) (@lem48679 A B C D _1321)). Qed.
Lemma lem48681 {A B C : Type'} (_1322 : type1656 A B C) : _1322 = _1322.
Proof. exact (eq_refl _1322). Qed.
Lemma lem48682 {A B C D : Type'} (_1321 : type1187 A B C D) (_1322 : type1656 A B C) : (@PASSOC A B C D _1321 _1322) = (term3 A B C D _1321 _1322).
Proof. exact (MK_COMB (@lem48680 A B C D _1321) (@lem48681 A B C _1322)). Qed.
Lemma lem48683 {A B C D : Type'} (_1321 : type1187 A B C D) (_1322 : type1656 A B C) : (term3 A B C D _1321 _1322) = (term4 A B C D _1321 _1322).
Proof. exact (eq_refl (term3 A B C D _1321 _1322)). Qed.
Lemma lem48684 {A B C D : Type'} (_1321 : type1187 A B C D) (_1322 : type1656 A B C) : (@PASSOC A B C D _1321 _1322) = (term4 A B C D _1321 _1322).
Proof. exact (TRANS (@lem48682 A B C D _1321 _1322) (@lem48683 A B C D _1321 _1322)). Qed.
Lemma lem48685 {A B C D : Type'} (_1321 : type1187 A B C D) : term5 A B C D _1321.
Proof. exact (fun _1322 : type1656 A B C => @lem48684 A B C D _1321 _1322). Qed.
Lemma lem48686 {A B C D : Type'} : term6 A B C D.
Proof. exact (fun _1321 : type1187 A B C D => @lem48685 A B C D _1321). Qed.
Lemma lem48687 {A B C D : Type'} (_1321 : type1187 A B C D) : term7 A B C D _1321.
Proof. exact (@lem48686 A B C D _1321). Qed.
Lemma lem48688 {A B C D : Type'} (_1321 : type1187 A B C D) : (term7 A B C D _1321) = (term5 A B C D _1321).
Proof. exact (eq_refl (term7 A B C D _1321)). Qed.
Lemma lem48689 {A B C D : Type'} (_1321 : type1187 A B C D) : term5 A B C D _1321.
Proof. exact (EQ_MP (@lem48688 A B C D _1321) (@lem48687 A B C D _1321)). Qed.
Lemma lem48690 {A B C D : Type'} (_1321 : type1187 A B C D) (_1322 : type1656 A B C) : term8 A B C D _1321 _1322.
Proof. exact (@lem48689 A B C D _1321 _1322). Qed.
Lemma lem48691 {A B C D : Type'} (_1321 : type1187 A B C D) (_1322 : type1656 A B C) : (term8 A B C D _1321 _1322) = ((@PASSOC A B C D _1321 _1322) = (term4 A B C D _1321 _1322)).
Proof. exact (eq_refl (term8 A B C D _1321 _1322)). Qed.
Lemma lem48692 {A B C D : Type'} (_1321 : type1187 A B C D) (_1322 : type1656 A B C) : (@PASSOC A B C D _1321 _1322) = (term4 A B C D _1321 _1322).
Proof. exact (EQ_MP (@lem48691 A B C D _1321 _1322) (@lem48690 A B C D _1321 _1322)). Qed.
Lemma lem48693 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) (z : C) : (term9 A B C D f x y z) = (term10 A B C D f x y z).
Proof. exact (@lem48692 A B C D f (term11 A B C x y z)). Qed.
Lemma lem48694 {A B : Type'} (x : A) : term12 A B x.
Proof. exact (@lem48019 A B x). Qed.
Lemma lem48695 {A B : Type'} (x : A) : (term12 A B x) = (term13 A B x).
Proof. exact (eq_refl (term12 A B x)). Qed.
Lemma lem48696 {A B : Type'} (x : A) : term13 A B x.
Proof. exact (EQ_MP (@lem48695 A B x) (@lem48694 A B x)). Qed.
Lemma lem48697 {A B : Type'} (x : A) (y : B) : term14 A B x y.
Proof. exact (@lem48696 A B x y). Qed.
Lemma lem48698 {A B : Type'} (x : A) (y : B) : (term14 A B x y) = ((term15 A B x y) = y).
Proof. exact (eq_refl (term14 A B x y)). Qed.
Lemma lem48700 {A B : Type'} (x : A) : term16 A B x.
Proof. exact (@lem47827 A B x). Qed.
Lemma lem48701 {A B : Type'} (x : A) : (term16 A B x) = (term17 A B x).
Proof. exact (eq_refl (term16 A B x)). Qed.
Lemma lem48702 {A B : Type'} (x : A) : term17 A B x.
Proof. exact (EQ_MP (@lem48701 A B x) (@lem48700 A B x)). Qed.
Lemma lem48703 {A B : Type'} (x : A) (y : B) : term18 A B x y.
Proof. exact (@lem48702 A B x y). Qed.
Lemma lem48704 {A B : Type'} (y : B) (x : A) : (term18 A B x y) = ((term19 A B x y) = x).
Proof. exact (eq_refl (term18 A B x y)). Qed.
Lemma lem48709 {A B : Type'} (y : B) (x : A) : (term19 A B x y) = x.
Proof. exact (EQ_MP (@lem48704 A B y x) (@lem48703 A B x y)). Qed.
Lemma lem48710 {A B C : Type'} (y : prod B C) (x : A) : (term20 A B C x y) = x.
Proof. exact (@lem48709 A (prod B C) y x). Qed.
Lemma lem48711 {A B C : Type'} (y : B) (z : C) (x : A) : (term21 A B C x y z) = x.
Proof. exact (@lem48710 A B C (@pair B C y z) x). Qed.
Lemma lem48712 {A B C : Type'} (x : A) (y : B) (z : C) : x = (term21 A B C x y z).
Proof. exact (SYM (@lem48711 A B C y z x)). Qed.
Lemma lem48714 {A B : Type'} (x : A) (y : B) : (term15 A B x y) = y.
Proof. exact (EQ_MP (@lem48698 A B x y) (@lem48697 A B x y)). Qed.
Lemma lem48715 {A B C : Type'} (x : A) (y : prod B C) : (term22 A B C x y) = y.
Proof. exact (@lem48714 A (prod B C) x y). Qed.
Lemma lem48716 {A B C : Type'} (x : A) (y : B) (z : C) : (term23 A B C x y z) = (@pair B C y z).
Proof. exact (@lem48715 A B C x (@pair B C y z)). Qed.
Lemma lem48717 {B C : Type'} : (@fst B C) = (@fst B C).
Proof. exact (eq_refl (@fst B C)). Qed.
Lemma lem48718 {A B C : Type'} (x : A) (y : B) (z : C) : (term24 A B C x y z) = (term19 B C y z).
Proof. exact (MK_COMB (@lem48717 B C) (@lem48716 A B C x y z)). Qed.
Lemma lem48720 {A B : Type'} (y : B) (x : A) : (term19 A B x y) = x.
Proof. exact (EQ_MP (@lem48704 A B y x) (@lem48703 A B x y)). Qed.
Lemma lem48721 {B C : Type'} (y : C) (x : B) : (term19 B C x y) = x.
Proof. exact (@lem48720 B C y x). Qed.
Lemma lem48722 {B C : Type'} (z : C) (y : B) : (term19 B C y z) = y.
Proof. exact (@lem48721 B C z y). Qed.
Lemma lem48723 {A B C : Type'} (x : A) (z : C) (y : B) : (term24 A B C x y z) = y.
Proof. exact (TRANS (@lem48718 A B C x y z) (@lem48722 B C z y)). Qed.
Lemma lem48724 {A B C : Type'} (x : A) (y : B) (z : C) : y = (term24 A B C x y z).
Proof. exact (SYM (@lem48723 A B C x z y)). Qed.
Lemma lem48726 {A B : Type'} (x : A) (y : B) : (term15 A B x y) = y.
Proof. exact (EQ_MP (@lem48698 A B x y) (@lem48697 A B x y)). Qed.
Lemma lem48727 {A B C : Type'} (x : A) (y : prod B C) : (term22 A B C x y) = y.
Proof. exact (@lem48726 A (prod B C) x y). Qed.
Lemma lem48728 {A B C : Type'} (x : A) (y : B) (z : C) : (term23 A B C x y z) = (@pair B C y z).
Proof. exact (@lem48727 A B C x (@pair B C y z)). Qed.
Lemma lem48729 {B C : Type'} : (@snd B C) = (@snd B C).
Proof. exact (eq_refl (@snd B C)). Qed.
Lemma lem48730 {A B C : Type'} (x : A) (y : B) (z : C) : (term25 A B C x y z) = (term15 B C y z).
Proof. exact (MK_COMB (@lem48729 B C) (@lem48728 A B C x y z)). Qed.
Lemma lem48732 {A B : Type'} (x : A) (y : B) : (term15 A B x y) = y.
Proof. exact (EQ_MP (@lem48698 A B x y) (@lem48697 A B x y)). Qed.
Lemma lem48733 {B C : Type'} (x : B) (y : C) : (term15 B C x y) = y.
Proof. exact (@lem48732 B C x y). Qed.
Lemma lem48734 {B C : Type'} (y : B) (z : C) : (term15 B C y z) = z.
Proof. exact (@lem48733 B C y z). Qed.
Lemma lem48735 {A B C : Type'} (x : A) (y : B) (z : C) : (term25 A B C x y z) = z.
Proof. exact (TRANS (@lem48730 A B C x y z) (@lem48734 B C y z)). Qed.
Lemma lem48736 {A B C : Type'} (x : A) (y : B) (z : C) : z = (term25 A B C x y z).
Proof. exact (SYM (@lem48735 A B C x y z)). Qed.
Lemma lem48738 {A B C D : Type'} (f : type1187 A B C D) : (term26 A B C D f) = (term26 A B C D f).
Proof. exact (eq_refl (term26 A B C D f)). Qed.
Lemma lem48739 {A B C D : Type'} (f : type1187 A B C D) : (term26 A B C D f) = (term27 A B C D f).
Proof. exact (eq_refl (term26 A B C D f)). Qed.
Lemma lem48740 {A B C D : Type'} (f : type1187 A B C D) : (term28 A B C D f) = (term28 A B C D f).
Proof. exact (eq_refl (term28 A B C D f)). Qed.
Lemma lem48741 {A B C D : Type'} (f : type1187 A B C D) : ((term26 A B C D f) = (term26 A B C D f)) = ((term26 A B C D f) = (term27 A B C D f)).
Proof. exact (MK_COMB (@lem48740 A B C D f) (@lem48739 A B C D f)). Qed.
Lemma lem48742 {A B C D : Type'} (f : type1187 A B C D) : (term26 A B C D f) = (term27 A B C D f).
Proof. exact (eq_refl (term26 A B C D f)). Qed.
Lemma lem48743 {A B C D : Type'} : (@eq (A -> B -> C -> D)) = (@eq (A -> B -> C -> D)).
Proof. exact (eq_refl (@eq (A -> B -> C -> D))). Qed.
Lemma lem48744 {A B C D : Type'} (f : type1187 A B C D) : (term28 A B C D f) = (term29 A B C D f).
Proof. exact (MK_COMB (@lem48743 A B C D) (@lem48742 A B C D f)). Qed.
Lemma lem48745 {A B C D : Type'} (f : type1187 A B C D) : (term27 A B C D f) = (term27 A B C D f).
Proof. exact (eq_refl (term27 A B C D f)). Qed.
Lemma lem48746 {A B C D : Type'} (f : type1187 A B C D) : ((term26 A B C D f) = (term27 A B C D f)) = ((term27 A B C D f) = (term27 A B C D f)).
Proof. exact (MK_COMB (@lem48744 A B C D f) (@lem48745 A B C D f)). Qed.
Lemma lem48747 {A B C D : Type'} (f : type1187 A B C D) : ((term26 A B C D f) = (term26 A B C D f)) = ((term27 A B C D f) = (term27 A B C D f)).
Proof. exact (TRANS (@lem48741 A B C D f) (@lem48746 A B C D f)). Qed.
Lemma lem48748 {A B C D : Type'} (f : type1187 A B C D) : (term27 A B C D f) = (term27 A B C D f).
Proof. exact (EQ_MP (@lem48747 A B C D f) (@lem48738 A B C D f)). Qed.
Lemma lem48749 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) (z : C) : (term30 A B C D f x) = (term31 A B C D f x y z).
Proof. exact (MK_COMB (@lem48748 A B C D f) (@lem48712 A B C x y z)). Qed.
Lemma lem48750 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) (z : C) : (term31 A B C D f x y z) = (term32 A B C D f x y z).
Proof. exact (eq_refl (term31 A B C D f x y z)). Qed.
Lemma lem48751 {A B C D : Type'} (f : type1187 A B C D) (x : A) : (term33 A B C D f x) = (term33 A B C D f x).
Proof. exact (eq_refl (term33 A B C D f x)). Qed.
Lemma lem48752 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) (z : C) : ((term30 A B C D f x) = (term31 A B C D f x y z)) = ((term30 A B C D f x) = (term32 A B C D f x y z)).
Proof. exact (MK_COMB (@lem48751 A B C D f x) (@lem48750 A B C D f x y z)). Qed.
Lemma lem48753 {A B C D : Type'} (f : type1187 A B C D) (x : A) : (term30 A B C D f x) = (term34 A B C D f x).
Proof. exact (eq_refl (term30 A B C D f x)). Qed.
Lemma lem48754 {B C D : Type'} : (@eq (B -> C -> D)) = (@eq (B -> C -> D)).
Proof. exact (eq_refl (@eq (B -> C -> D))). Qed.
Lemma lem48755 {A B C D : Type'} (f : type1187 A B C D) (x : A) : (term33 A B C D f x) = (term35 A B C D f x).
Proof. exact (MK_COMB (@lem48754 B C D) (@lem48753 A B C D f x)). Qed.
Lemma lem48756 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) (z : C) : (term32 A B C D f x y z) = (term32 A B C D f x y z).
Proof. exact (eq_refl (term32 A B C D f x y z)). Qed.
Lemma lem48757 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) (z : C) : ((term30 A B C D f x) = (term32 A B C D f x y z)) = ((term34 A B C D f x) = (term32 A B C D f x y z)).
Proof. exact (MK_COMB (@lem48755 A B C D f x) (@lem48756 A B C D f x y z)). Qed.
Lemma lem48758 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) (z : C) : ((term30 A B C D f x) = (term31 A B C D f x y z)) = ((term34 A B C D f x) = (term32 A B C D f x y z)).
Proof. exact (TRANS (@lem48752 A B C D f x y z) (@lem48757 A B C D f x y z)). Qed.
Lemma lem48759 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) (z : C) : (term34 A B C D f x) = (term32 A B C D f x y z).
Proof. exact (EQ_MP (@lem48758 A B C D f x y z) (@lem48749 A B C D f x y z)). Qed.
Lemma lem48760 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) (z : C) : (term36 A B C D f x y) = (term37 A B C D f x y z).
Proof. exact (MK_COMB (@lem48759 A B C D f x y z) (@lem48724 A B C x y z)). Qed.
Lemma lem48761 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) (z : C) : (term37 A B C D f x y z) = (term38 A B C D f x y z).
Proof. exact (eq_refl (term37 A B C D f x y z)). Qed.
Lemma lem48762 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) : (term39 A B C D f x y) = (term39 A B C D f x y).
Proof. exact (eq_refl (term39 A B C D f x y)). Qed.
Lemma lem48763 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) (z : C) : ((term36 A B C D f x y) = (term37 A B C D f x y z)) = ((term36 A B C D f x y) = (term38 A B C D f x y z)).
Proof. exact (MK_COMB (@lem48762 A B C D f x y) (@lem48761 A B C D f x y z)). Qed.
Lemma lem48764 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) : (term36 A B C D f x y) = (term40 A B C D f x y).
Proof. exact (eq_refl (term36 A B C D f x y)). Qed.
Lemma lem48765 {C D : Type'} : (@eq (C -> D)) = (@eq (C -> D)).
Proof. exact (eq_refl (@eq (C -> D))). Qed.
Lemma lem48766 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) : (term39 A B C D f x y) = (term41 A B C D f x y).
Proof. exact (MK_COMB (@lem48765 C D) (@lem48764 A B C D f x y)). Qed.
Lemma lem48767 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) (z : C) : (term38 A B C D f x y z) = (term38 A B C D f x y z).
Proof. exact (eq_refl (term38 A B C D f x y z)). Qed.
Lemma lem48768 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) (z : C) : ((term36 A B C D f x y) = (term38 A B C D f x y z)) = ((term40 A B C D f x y) = (term38 A B C D f x y z)).
Proof. exact (MK_COMB (@lem48766 A B C D f x y) (@lem48767 A B C D f x y z)). Qed.
Lemma lem48769 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) (z : C) : ((term36 A B C D f x y) = (term37 A B C D f x y z)) = ((term40 A B C D f x y) = (term38 A B C D f x y z)).
Proof. exact (TRANS (@lem48763 A B C D f x y z) (@lem48768 A B C D f x y z)). Qed.
Lemma lem48770 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) (z : C) : (term40 A B C D f x y) = (term38 A B C D f x y z).
Proof. exact (EQ_MP (@lem48769 A B C D f x y z) (@lem48760 A B C D f x y z)). Qed.
Lemma lem48771 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) (z : C) : (term42 A B C D f x y z) = (term43 A B C D f x y z).
Proof. exact (MK_COMB (@lem48770 A B C D f x y z) (@lem48736 A B C x y z)). Qed.
Lemma lem48772 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) (z : C) : (term43 A B C D f x y z) = (term10 A B C D f x y z).
Proof. exact (eq_refl (term43 A B C D f x y z)). Qed.
Lemma lem48773 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) (z : C) : (term44 A B C D f x y z) = (term44 A B C D f x y z).
Proof. exact (eq_refl (term44 A B C D f x y z)). Qed.
Lemma lem48774 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) (z : C) : ((term42 A B C D f x y z) = (term43 A B C D f x y z)) = ((term42 A B C D f x y z) = (term10 A B C D f x y z)).
Proof. exact (MK_COMB (@lem48773 A B C D f x y z) (@lem48772 A B C D f x y z)). Qed.
Lemma lem48775 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) (z : C) : (term42 A B C D f x y z) = (term45 A B C D f x y z).
Proof. exact (eq_refl (term42 A B C D f x y z)). Qed.
Lemma lem48776 {D : Type'} : (@eq D) = (@eq D).
Proof. exact (eq_refl (@eq D)). Qed.
Lemma lem48777 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) (z : C) : (term44 A B C D f x y z) = (term46 A B C D f x y z).
Proof. exact (MK_COMB (@lem48776 D) (@lem48775 A B C D f x y z)). Qed.
Lemma lem48778 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) (z : C) : (term10 A B C D f x y z) = (term10 A B C D f x y z).
Proof. exact (eq_refl (term10 A B C D f x y z)). Qed.
Lemma lem48779 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) (z : C) : ((term42 A B C D f x y z) = (term10 A B C D f x y z)) = ((term45 A B C D f x y z) = (term10 A B C D f x y z)).
Proof. exact (MK_COMB (@lem48777 A B C D f x y z) (@lem48778 A B C D f x y z)). Qed.
Lemma lem48780 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) (z : C) : ((term42 A B C D f x y z) = (term43 A B C D f x y z)) = ((term45 A B C D f x y z) = (term10 A B C D f x y z)).
Proof. exact (TRANS (@lem48774 A B C D f x y z) (@lem48779 A B C D f x y z)). Qed.
Lemma lem48781 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) (z : C) : (term45 A B C D f x y z) = (term10 A B C D f x y z).
Proof. exact (EQ_MP (@lem48780 A B C D f x y z) (@lem48771 A B C D f x y z)). Qed.
Lemma lem48782 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) (z : C) : (term10 A B C D f x y z) = (term45 A B C D f x y z).
Proof. exact (SYM (@lem48781 A B C D f x y z)). Qed.
Lemma lem48783 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) (z : C) : (term9 A B C D f x y z) = (term45 A B C D f x y z).
Proof. exact (TRANS (@lem48693 A B C D f x y z) (@lem48782 A B C D f x y z)). Qed.
Lemma lem48784 {A B C D : Type'} (f : type1187 A B C D) (x : A) (y : B) : term47 A B C D f x y.
Proof. exact (fun z : C => @lem48783 A B C D f x y z). Qed.
Lemma lem48785 {A B C D : Type'} (f : type1187 A B C D) (x : A) : term48 A B C D f x.
Proof. exact (fun y : B => @lem48784 A B C D f x y). Qed.
Lemma lem48786 {A B C D : Type'} (f : type1187 A B C D) : term49 A B C D f.
Proof. exact (fun x : A => @lem48785 A B C D f x). Qed.
Lemma lem48787 {A B C D : Type'} : term50 A B C D.
Proof. exact (fun f : type1187 A B C D => @lem48786 A B C D f). Qed.
