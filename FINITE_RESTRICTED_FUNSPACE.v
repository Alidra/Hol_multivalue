Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_RESTRICTED_FUNSPACE_term_abbrevs.
Require Import CONJ_ASSOC_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FINITE_CROSS_spec.
Require Import FINITE_IMAGE_spec.
Require Import FINITE_POWERSET_spec.
Require Import FINITE_SUBSET_spec.
Require Import FORALL_IN_GSPEC_spec.
Require Import FORALL_IN_IMAGE_spec.
Require Import FUN_EQ_THM_spec.
Require Import IN_CROSS_spec.
Require Import IN_IMAGE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import PAIR_EQ_spec.
Require Import SUBSET_spec.
Require Import UNWIND_THM1_spec.
Require Import UNWIND_THM2_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
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
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm9523_spec.
Require Import thm9524_spec.
Lemma lem4617673 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : term0 A B f k x.
Proof. exact (@lem9784 ((f x) = (k x))). Qed.
Lemma lem4617674 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term0 A B f k x) = (term1 A B f k x).
Proof. exact (eq_refl (term0 A B f k x)). Qed.
Lemma lem4617675 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : term1 A B f k x.
Proof. exact (EQ_MP (@lem4617674 A B f k x) (@lem4617673 A B f k x)). Qed.
Lemma lem4617677 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : term2 A B f k x.
Proof. exact (h1). Qed.
Lemma lem4617681 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term3 t1 t2 t3) = (term4 t1 t2 t3)) : (term3 t1 t2 t3) = (term4 t1 t2 t3).
Proof. exact (h1). Qed.
Lemma lem4617682 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term3 t1 t2 t3) = (term4 t1 t2 t3)) : (term4 t1 t2 t3) = (term3 t1 t2 t3).
Proof. exact (SYM (@lem4617681 t1 t2 t3 h1)). Qed.
Lemma lem4617683 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term4 t1 t2 t3) = (term3 t1 t2 t3)) : (term4 t1 t2 t3) = (term3 t1 t2 t3).
Proof. exact (h1). Qed.
Lemma lem4617684 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term4 t1 t2 t3) = (term3 t1 t2 t3)) : (term3 t1 t2 t3) = (term4 t1 t2 t3).
Proof. exact (SYM (@lem4617683 t1 t2 t3 h1)). Qed.
Lemma lem4617685 (t1 : Prop) (t2 : Prop) (t3 : Prop) : ((term3 t1 t2 t3) = (term4 t1 t2 t3)) = ((term4 t1 t2 t3) = (term3 t1 t2 t3)).
Proof. exact (prop_ext (fun h1 : (term3 t1 t2 t3) = (term4 t1 t2 t3) => @lem4617682 t1 t2 t3 h1) (fun h1 : (term4 t1 t2 t3) = (term3 t1 t2 t3) => @lem4617684 t1 t2 t3 h1)). Qed.
Lemma lem4617686 (t1 : Prop) (t2 : Prop) : (term5 t1 t2) = (term6 t1 t2).
Proof. exact (fun_ext (fun t3 : Prop => @lem4617685 t1 t2 t3)). Qed.
Lemma lem4617687 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem4617688 (t1 : Prop) (t2 : Prop) : (term7 t1 t2) = (term8 t1 t2).
Proof. exact (MK_COMB (@lem4617687) (@lem4617686 t1 t2)). Qed.
Lemma lem4617689 (t1 : Prop) : (term9 t1) = (term10 t1).
Proof. exact (fun_ext (fun t2 : Prop => @lem4617688 t1 t2)). Qed.
Lemma lem4617690 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem4617691 (t1 : Prop) : (term11 t1) = (term12 t1).
Proof. exact (MK_COMB (@lem4617690) (@lem4617689 t1)). Qed.
Lemma lem4617692 : term13 = term14.
Proof. exact (fun_ext (fun t1 : Prop => @lem4617691 t1)). Qed.
Lemma lem4617693 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem4617694 : term15 = term16.
Proof. exact (MK_COMB (@lem4617693) (@lem4617692)). Qed.
Lemma lem4617695 : term16.
Proof. exact (EQ_MP (@lem4617694) (@lem512)). Qed.
Lemma lem4617696 {A : Type'} (P : A -> Prop) : term17 A P.
Proof. exact (@lem4564 A P). Qed.
Lemma lem4617697 {A : Type'} (P : A -> Prop) : (term17 A P) = (term18 A P).
Proof. exact (eq_refl (term17 A P)). Qed.
Lemma lem4617698 {A : Type'} (P : A -> Prop) : term18 A P.
Proof. exact (EQ_MP (@lem4617697 A P) (@lem4617696 A P)). Qed.
Lemma lem4617699 {A : Type'} (P : A -> Prop) (a : A) : term19 A P a.
Proof. exact (@lem4617698 A P a). Qed.
Lemma lem4617700 {A : Type'} (P : A -> Prop) (a : A) : (term19 A P a) = ((term20 A a P) = (P a)).
Proof. exact (eq_refl (term19 A P a)). Qed.
Lemma lem4617702 {A : Type'} (P : A -> Prop) : term21 A P.
Proof. exact (@lem4524 A P). Qed.
Lemma lem4617703 {A : Type'} (P : A -> Prop) : (term21 A P) = (term22 A P).
Proof. exact (eq_refl (term21 A P)). Qed.
Lemma lem4617704 {A : Type'} (P : A -> Prop) : term22 A P.
Proof. exact (EQ_MP (@lem4617703 A P) (@lem4617702 A P)). Qed.
Lemma lem4617705 {A : Type'} (P : A -> Prop) (a : A) : term23 A P a.
Proof. exact (@lem4617704 A P a). Qed.
Lemma lem4617706 {A : Type'} (P : A -> Prop) (a : A) : (term23 A P a) = ((term24 A a P) = (P a)).
Proof. exact (eq_refl (term23 A P a)). Qed.
Lemma lem4617708 (t1 : Prop) : term25 t1.
Proof. exact (@lem4617695 t1). Qed.
Lemma lem4617709 (t1 : Prop) : (term25 t1) = (term12 t1).
Proof. exact (eq_refl (term25 t1)). Qed.
Lemma lem4617710 (t1 : Prop) : term12 t1.
Proof. exact (EQ_MP (@lem4617709 t1) (@lem4617708 t1)). Qed.
Lemma lem4617711 (t1 : Prop) (t2 : Prop) : term26 t1 t2.
Proof. exact (@lem4617710 t1 t2). Qed.
Lemma lem4617712 (t1 : Prop) (t2 : Prop) : (term26 t1 t2) = (term8 t1 t2).
Proof. exact (eq_refl (term26 t1 t2)). Qed.
Lemma lem4617713 (t1 : Prop) (t2 : Prop) : term8 t1 t2.
Proof. exact (EQ_MP (@lem4617712 t1 t2) (@lem4617711 t1 t2)). Qed.
Lemma lem4617714 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term27 t1 t2 t3.
Proof. exact (@lem4617713 t1 t2 t3). Qed.
Lemma lem4617715 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term27 t1 t2 t3) = ((term4 t1 t2 t3) = (term3 t1 t2 t3)).
Proof. exact (eq_refl (term27 t1 t2 t3)). Qed.
Lemma lem4617717 {A B : Type'} (x : A) : term28 A B x.
Proof. exact (@lem47438 A B x). Qed.
Lemma lem4617718 {A B : Type'} (x : A) : (term28 A B x) = (term29 A B x).
Proof. exact (eq_refl (term28 A B x)). Qed.
Lemma lem4617719 {A B : Type'} (x : A) : term29 A B x.
Proof. exact (EQ_MP (@lem4617718 A B x) (@lem4617717 A B x)). Qed.
Lemma lem4617720 {A B : Type'} (x : A) (y : B) : term30 A B x y.
Proof. exact (@lem4617719 A B x y). Qed.
Lemma lem4617721 {A B : Type'} (x : A) (y : B) : (term30 A B x y) = (term31 A B x y).
Proof. exact (eq_refl (term30 A B x y)). Qed.
Lemma lem4617722 {A B : Type'} (x : A) (y : B) : term31 A B x y.
Proof. exact (EQ_MP (@lem4617721 A B x y) (@lem4617720 A B x y)). Qed.
Lemma lem4617723 {A B : Type'} (x : A) (y : B) (a : A) : term32 A B x y a.
Proof. exact (@lem4617722 A B x y a). Qed.
Lemma lem4617724 {A B : Type'} (x : A) (a : A) (y : B) : (term32 A B x y a) = (term33 A B x a y).
Proof. exact (eq_refl (term32 A B x y a)). Qed.
Lemma lem4617725 {A B : Type'} (x : A) (a : A) (y : B) : term33 A B x a y.
Proof. exact (EQ_MP (@lem4617724 A B x a y) (@lem4617723 A B x y a)). Qed.
Lemma lem4617726 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : term34 A B x a y b.
Proof. exact (@lem4617725 A B x a y b). Qed.
Lemma lem4617727 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term34 A B x a y b) = (((@pair A B x y) = (@pair A B a b)) = (term35 A B x a y b)).
Proof. exact (eq_refl (term34 A B x a y b)). Qed.
Lemma lem4617753 {_83095 : Type'} : term36 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4617754 {_83095 : Type'} (p : _83095 -> Prop) : term37 _83095 p.
Proof. exact (@lem4617753 _83095 p). Qed.
Lemma lem4617755 {_83095 : Type'} (p : _83095 -> Prop) : (term37 _83095 p) = (term38 _83095 p).
Proof. exact (eq_refl (term37 _83095 p)). Qed.
Lemma lem4617756 {_83095 : Type'} (p : _83095 -> Prop) : term38 _83095 p.
Proof. exact (EQ_MP (@lem4617755 _83095 p) (@lem4617754 _83095 p)). Qed.
Lemma lem4617757 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term39 _83095 p x.
Proof. exact (@lem4617756 _83095 p x). Qed.
Lemma lem4617758 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term39 _83095 p x) = ((term40 _83095 x p) = (p x)).
Proof. exact (eq_refl (term39 _83095 p x)). Qed.
Lemma lem4617767 {A B : Type'} (y : B) : term41 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem4617768 {A B : Type'} (y : B) : (term41 A B y) = (term42 A B y).
Proof. exact (eq_refl (term41 A B y)). Qed.
Lemma lem4617769 {A B : Type'} (y : B) : term42 A B y.
Proof. exact (EQ_MP (@lem4617768 A B y) (@lem4617767 A B y)). Qed.
Lemma lem4617770 {A B : Type'} (y : B) (s : A -> Prop) : term43 A B y s.
Proof. exact (@lem4617769 A B y s). Qed.
Lemma lem4617771 {A B : Type'} (y : B) (s : A -> Prop) : (term43 A B y s) = (term44 A B y s).
Proof. exact (eq_refl (term43 A B y s)). Qed.
Lemma lem4617772 {A B : Type'} (y : B) (s : A -> Prop) : term44 A B y s.
Proof. exact (EQ_MP (@lem4617771 A B y s) (@lem4617770 A B y s)). Qed.
Lemma lem4617773 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term45 A B y s f.
Proof. exact (@lem4617772 A B y s f). Qed.
Lemma lem4617774 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term45 A B y s f) = ((term46 A B y f s) = (term47 A B y f s)).
Proof. exact (eq_refl (term45 A B y s f)). Qed.
Lemma lem4617776 {A B : Type'} (f : A -> B) : term48 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem4617777 {A B : Type'} (f : A -> B) : (term48 A B f) = (term49 A B f).
Proof. exact (eq_refl (term48 A B f)). Qed.
Lemma lem4617778 {A B : Type'} (f : A -> B) : term49 A B f.
Proof. exact (EQ_MP (@lem4617777 A B f) (@lem4617776 A B f)). Qed.
Lemma lem4617779 {A B : Type'} (f : A -> B) (g : A -> B) : term50 A B f g.
Proof. exact (@lem4617778 A B f g). Qed.
Lemma lem4617780 {A B : Type'} (f : A -> B) (g : A -> B) : (term50 A B f g) = ((f = g) = (term51 A B f g)).
Proof. exact (eq_refl (term50 A B f g)). Qed.
Lemma lem4617782 {_103718 _103721 : Type'} (x : _103718) : term52 _103718 _103721 x.
Proof. exact (@lem4325365 _103718 _103721 x). Qed.
Lemma lem4617783 {_103718 _103721 : Type'} (x : _103718) : (term52 _103718 _103721 x) = (term53 _103718 _103721 x).
Proof. exact (eq_refl (term52 _103718 _103721 x)). Qed.
Lemma lem4617784 {_103718 _103721 : Type'} (x : _103718) : term53 _103718 _103721 x.
Proof. exact (EQ_MP (@lem4617783 _103718 _103721 x) (@lem4617782 _103718 _103721 x)). Qed.
Lemma lem4617785 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term54 _103718 _103721 x y.
Proof. exact (@lem4617784 _103718 _103721 x y). Qed.
Lemma lem4617786 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : (term54 _103718 _103721 x y) = (term55 _103718 _103721 x y).
Proof. exact (eq_refl (term54 _103718 _103721 x y)). Qed.
Lemma lem4617787 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term55 _103718 _103721 x y.
Proof. exact (EQ_MP (@lem4617786 _103718 _103721 x y) (@lem4617785 _103718 _103721 x y)). Qed.
Lemma lem4617788 {_103718 _103721 : Type'} (x : _103718) (y : _103721) (s : _103718 -> Prop) : term56 _103718 _103721 x y s.
Proof. exact (@lem4617787 _103718 _103721 x y s). Qed.
Lemma lem4617789 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : (term56 _103718 _103721 x y s) = (term57 _103718 _103721 x s y).
Proof. exact (eq_refl (term56 _103718 _103721 x y s)). Qed.
Lemma lem4617790 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : term57 _103718 _103721 x s y.
Proof. exact (EQ_MP (@lem4617789 _103718 _103721 x s y) (@lem4617788 _103718 _103721 x y s)). Qed.
Lemma lem4617791 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : term58 _103718 _103721 x s y t.
Proof. exact (@lem4617790 _103718 _103721 x s y t). Qed.
Lemma lem4617792 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term58 _103718 _103721 x s y t) = ((term59 _103718 _103721 x y s t) = (term60 _103718 _103721 x s y t)).
Proof. exact (eq_refl (term58 _103718 _103721 x s y t)). Qed.
Lemma lem4617818 {_83095 : Type'} : term36 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4617819 {_83095 : Type'} (p : _83095 -> Prop) : term37 _83095 p.
Proof. exact (@lem4617818 _83095 p). Qed.
Lemma lem4617820 {_83095 : Type'} (p : _83095 -> Prop) : (term37 _83095 p) = (term38 _83095 p).
Proof. exact (eq_refl (term37 _83095 p)). Qed.
Lemma lem4617821 {_83095 : Type'} (p : _83095 -> Prop) : term38 _83095 p.
Proof. exact (EQ_MP (@lem4617820 _83095 p) (@lem4617819 _83095 p)). Qed.
Lemma lem4617822 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term39 _83095 p x.
Proof. exact (@lem4617821 _83095 p x). Qed.
Lemma lem4617823 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term39 _83095 p x) = ((term40 _83095 x p) = (p x)).
Proof. exact (eq_refl (term39 _83095 p x)). Qed.
Lemma lem4617832 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term61 _87967 _87968 P f.
Proof. exact (@lem3386920 _87967 _87968 P f). Qed.
Lemma lem4617833 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : (term61 _87967 _87968 P f) = (term62 _87967 _87968 P f).
Proof. exact (eq_refl (term61 _87967 _87968 P f)). Qed.
Lemma lem4617834 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term62 _87967 _87968 P f.
Proof. exact (EQ_MP (@lem4617833 _87967 _87968 P f) (@lem4617832 _87967 _87968 P f)). Qed.
Lemma lem4617835 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (s : _87968 -> Prop) : term63 _87967 _87968 P f s.
Proof. exact (@lem4617834 _87967 _87968 P f s). Qed.
Lemma lem4617836 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term63 _87967 _87968 P f s) = ((term64 _87967 _87968 f s P) = (term65 _87967 _87968 s P f)).
Proof. exact (eq_refl (term63 _87967 _87968 P f s)). Qed.
Lemma lem4617838 {A : Type'} (s : A -> Prop) : term66 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem4617839 {A : Type'} (s : A -> Prop) : (term66 A s) = (term67 A s).
Proof. exact (eq_refl (term66 A s)). Qed.
Lemma lem4617840 {A : Type'} (s : A -> Prop) : term67 A s.
Proof. exact (EQ_MP (@lem4617839 A s) (@lem4617838 A s)). Qed.
Lemma lem4617841 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term68 A s t.
Proof. exact (@lem4617840 A s t). Qed.
Lemma lem4617842 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term68 A s t) = ((@SUBSET A s t) = (term69 A s t)).
Proof. exact (eq_refl (term68 A s t)). Qed.
Lemma lem4617868 {_83095 : Type'} : term36 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4617869 {_83095 : Type'} (p : _83095 -> Prop) : term37 _83095 p.
Proof. exact (@lem4617868 _83095 p). Qed.
Lemma lem4617870 {_83095 : Type'} (p : _83095 -> Prop) : (term37 _83095 p) = (term38 _83095 p).
Proof. exact (eq_refl (term37 _83095 p)). Qed.
Lemma lem4617871 {_83095 : Type'} (p : _83095 -> Prop) : term38 _83095 p.
Proof. exact (EQ_MP (@lem4617870 _83095 p) (@lem4617869 _83095 p)). Qed.
Lemma lem4617872 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term39 _83095 p x.
Proof. exact (@lem4617871 _83095 p x). Qed.
Lemma lem4617873 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term39 _83095 p x) = ((term40 _83095 x p) = (p x)).
Proof. exact (eq_refl (term39 _83095 p x)). Qed.
Lemma lem4617882 {A B : Type'} (y : B) : term41 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem4617883 {A B : Type'} (y : B) : (term41 A B y) = (term42 A B y).
Proof. exact (eq_refl (term41 A B y)). Qed.
Lemma lem4617884 {A B : Type'} (y : B) : term42 A B y.
Proof. exact (EQ_MP (@lem4617883 A B y) (@lem4617882 A B y)). Qed.
Lemma lem4617885 {A B : Type'} (y : B) (s : A -> Prop) : term43 A B y s.
Proof. exact (@lem4617884 A B y s). Qed.
Lemma lem4617886 {A B : Type'} (y : B) (s : A -> Prop) : (term43 A B y s) = (term44 A B y s).
Proof. exact (eq_refl (term43 A B y s)). Qed.
Lemma lem4617887 {A B : Type'} (y : B) (s : A -> Prop) : term44 A B y s.
Proof. exact (EQ_MP (@lem4617886 A B y s) (@lem4617885 A B y s)). Qed.
Lemma lem4617888 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term45 A B y s f.
Proof. exact (@lem4617887 A B y s f). Qed.
Lemma lem4617889 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term45 A B y s f) = ((term46 A B y f s) = (term47 A B y f s)).
Proof. exact (eq_refl (term45 A B y s f)). Qed.
Lemma lem4617914 {_88905 _89106 : Type'} (Q : _89106 -> Prop) : term70 _88905 _89106 Q.
Proof. exact (proj1 (@lem3435744 _88905 Prop Prop Prop Prop Prop _89106 Prop Prop Prop Prop Q)). Qed.
Lemma lem4617915 {_88905 _89106 : Type'} (Q : _89106 -> Prop) (P : _88905 -> Prop) : term71 _88905 _89106 Q P.
Proof. exact (@lem4617914 _88905 _89106 Q P). Qed.
Lemma lem4617916 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) : (term71 _88905 _89106 Q P) = (term72 _88905 _89106 P Q).
Proof. exact (eq_refl (term71 _88905 _89106 Q P)). Qed.
Lemma lem4617917 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) : term72 _88905 _89106 P Q.
Proof. exact (EQ_MP (@lem4617916 _88905 _89106 P Q) (@lem4617915 _88905 _89106 Q P)). Qed.
Lemma lem4617918 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) (f : _88905 -> _89106) : term73 _88905 _89106 P Q f.
Proof. exact (@lem4617917 _88905 _89106 P Q f). Qed.
Lemma lem4617919 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) (f : _88905 -> _89106) : (term73 _88905 _89106 P Q f) = ((term74 _88905 _89106 P f Q) = (term75 _88905 _89106 P Q f)).
Proof. exact (eq_refl (term73 _88905 _89106 P Q f)). Qed.
Lemma lem4617921 {A : Type'} (s : A -> Prop) : term66 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem4617922 {A : Type'} (s : A -> Prop) : (term66 A s) = (term67 A s).
Proof. exact (eq_refl (term66 A s)). Qed.
Lemma lem4617923 {A : Type'} (s : A -> Prop) : term67 A s.
Proof. exact (EQ_MP (@lem4617922 A s) (@lem4617921 A s)). Qed.
Lemma lem4617924 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term68 A s t.
Proof. exact (@lem4617923 A s t). Qed.
Lemma lem4617925 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term68 A s t) = ((@SUBSET A s t) = (term69 A s t)).
Proof. exact (eq_refl (term68 A s t)). Qed.
Lemma lem4617927 {A : Type'} (h1 : term76 A) : term76 A.
Proof. exact (h1). Qed.
Lemma lem4617928 {A : Type'} (s : A -> Prop) (h1 : term76 A) : term77 A s.
Proof. exact (@lem4617927 A h1 s). Qed.
Lemma lem4617929 {A : Type'} (s : A -> Prop) : (term77 A s) = (term78 A s).
Proof. exact (eq_refl (term77 A s)). Qed.
Lemma lem4617930 {A : Type'} (s : A -> Prop) (h1 : term76 A) : term78 A s.
Proof. exact (EQ_MP (@lem4617929 A s) (@lem4617928 A s h1)). Qed.
Lemma lem4617931 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term76 A) : term79 A s t.
Proof. exact (@lem4617930 A s h1 t). Qed.
Lemma lem4617932 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term79 A s t) = (term80 A t s).
Proof. exact (eq_refl (term79 A s t)). Qed.
Lemma lem4617933 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term76 A) : term80 A t s.
Proof. exact (EQ_MP (@lem4617932 A t s) (@lem4617931 A s t h1)). Qed.
Lemma lem4617934 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term81 A s t) : term81 A s t.
Proof. exact (h1). Qed.
Lemma lem4617935 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term76 A) (h2 : term81 A s t) : @FINITE A s.
Proof. exact (@lem4617933 A t s h1 (@lem4617934 A s t h2)). Qed.
Lemma lem4617936 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term81 A s t) : term82 A s.
Proof. exact (fun h0 : term76 A => @lem4617935 A s t h0 h1). Qed.
Lemma lem4617937 {A : Type'} (s : A -> Prop) (h1 : term83 A s) : term83 A s.
Proof. exact (h1). Qed.
Lemma lem4617938 {A : Type'} (s : A -> Prop) (h1 : term83 A s) : term82 A s.
Proof. exact (ex_elim (@lem4617937 A s h1) (fun t : A -> Prop => fun h0 : term84 A s t => @lem4617936 A s t h0)). Qed.
Lemma lem4617939 {A : Type'} (h1 : term76 A) : term76 A.
Proof. exact (h1). Qed.
Lemma lem4617940 {A : Type'} (s : A -> Prop) (h1 : term76 A) (h2 : term83 A s) : @FINITE A s.
Proof. exact (@lem4617938 A s h2 (@lem4617939 A h1)). Qed.
Lemma lem4617941 {A : Type'} (s : A -> Prop) (h1 : term76 A) : term85 A s.
Proof. exact (fun h0 : term83 A s => @lem4617940 A s h1 h0). Qed.
Lemma lem4617942 {A : Type'} (h1 : term76 A) : term86 A.
Proof. exact (fun s : A -> Prop => @lem4617941 A s h1). Qed.
Lemma lem4617943 {A : Type'} : term87 A.
Proof. exact (fun h0 : term76 A => @lem4617942 A h0). Qed.
Lemma lem4617944 {A : Type'} : term86 A.
Proof. exact (@lem4617943 A (@lem3599924 A)). Qed.
Lemma lem4617945 {A : Type'} (s : A -> Prop) : term88 A s.
Proof. exact (@lem4617944 A s). Qed.
Lemma lem4617946 {A : Type'} (s : A -> Prop) : (term88 A s) = (term85 A s).
Proof. exact (eq_refl (term88 A s)). Qed.
Lemma lem4617948 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term89 A B s t) : term89 A B s t.
Proof. exact (h1). Qed.
Lemma lem4617949 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem4617950 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4617952 {A : Type'} (s : A -> Prop) : term85 A s.
Proof. exact (EQ_MP (@lem4617946 A s) (@lem4617945 A s)). Qed.
Lemma lem4617953 {A B : Type'} (s : type572 A B) : term90 A B s.
Proof. exact (@lem4617952 (A -> B) s). Qed.
Lemma lem4617954 {A B : Type'} (t : B -> Prop) (k : A -> B) (s : A -> Prop) : term91 A B t k s.
Proof. exact (@lem4617953 A B (term92 A B t k s)). Qed.
Lemma lem4617955 {A B : Type'} (f : A -> B) : term93 A B f.
Proof. exact (@lem3615104 A B f). Qed.
Lemma lem4617956 {A B : Type'} (f : A -> B) : (term93 A B f) = (term94 A B f).
Proof. exact (eq_refl (term93 A B f)). Qed.
Lemma lem4617957 {A B : Type'} (f : A -> B) : term94 A B f.
Proof. exact (EQ_MP (@lem4617956 A B f) (@lem4617955 A B f)). Qed.
Lemma lem4617958 {A B : Type'} (f : A -> B) (s : A -> Prop) : term95 A B f s.
Proof. exact (@lem4617957 A B f s). Qed.
Lemma lem4617959 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term95 A B f s) = (term96 A B f s).
Proof. exact (eq_refl (term95 A B f s)). Qed.
Lemma lem4617960 {A B : Type'} (f : A -> B) (s : A -> Prop) : term96 A B f s.
Proof. exact (EQ_MP (@lem4617959 A B f s) (@lem4617958 A B f s)). Qed.
Lemma lem4617961 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4617962 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term97 A B f s.
Proof. exact (@lem4617960 A B f s (@lem4617961 A s h1)). Qed.
Lemma lem4617963 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term97 A B f s) = ((term97 A B f s) = True).
Proof. exact (@lem7 (term97 A B f s)). Qed.
Lemma lem4617964 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term97 A B f s) = True.
Proof. exact (EQ_MP (@lem4617963 A B f s) (@lem4617962 A B f s h1)). Qed.
Lemma lem4617970 {_103774 _103776 : Type'} (s : _103774 -> Prop) : term98 _103774 _103776 s.
Proof. exact (@lem4325576 _103774 _103776 s). Qed.
Lemma lem4617971 {_103774 _103776 : Type'} (s : _103774 -> Prop) : (term98 _103774 _103776 s) = (term99 _103774 _103776 s).
Proof. exact (eq_refl (term98 _103774 _103776 s)). Qed.
Lemma lem4617972 {_103774 _103776 : Type'} (s : _103774 -> Prop) : term99 _103774 _103776 s.
Proof. exact (EQ_MP (@lem4617971 _103774 _103776 s) (@lem4617970 _103774 _103776 s)). Qed.
Lemma lem4617973 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) : term100 _103774 _103776 s t.
Proof. exact (@lem4617972 _103774 _103776 s t). Qed.
Lemma lem4617974 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) : (term100 _103774 _103776 s t) = (term101 _103774 _103776 s t).
Proof. exact (eq_refl (term100 _103774 _103776 s t)). Qed.
Lemma lem4617975 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) : term101 _103774 _103776 s t.
Proof. exact (EQ_MP (@lem4617974 _103774 _103776 s t) (@lem4617973 _103774 _103776 s t)). Qed.
Lemma lem4617976 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) (h1 : term89 _103774 _103776 s t) : term89 _103774 _103776 s t.
Proof. exact (h1). Qed.
Lemma lem4617977 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) (h1 : term89 _103774 _103776 s t) : term102 _103774 _103776 s t.
Proof. exact (@lem4617975 _103774 _103776 s t (@lem4617976 _103774 _103776 s t h1)). Qed.
Lemma lem4617978 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) : (term102 _103774 _103776 s t) = ((term102 _103774 _103776 s t) = True).
Proof. exact (@lem7 (term102 _103774 _103776 s t)). Qed.
Lemma lem4617979 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) (h1 : term89 _103774 _103776 s t) : (term102 _103774 _103776 s t) = True.
Proof. exact (EQ_MP (@lem4617978 _103774 _103776 s t) (@lem4617977 _103774 _103776 s t h1)). Qed.
Lemma lem4617985 {A : Type'} (s : A -> Prop) : term103 A s.
Proof. exact (@lem4603107 A s). Qed.
Lemma lem4617986 {A : Type'} (s : A -> Prop) : (term103 A s) = (term104 A s).
Proof. exact (eq_refl (term103 A s)). Qed.
Lemma lem4617987 {A : Type'} (s : A -> Prop) : term104 A s.
Proof. exact (EQ_MP (@lem4617986 A s) (@lem4617985 A s)). Qed.
Lemma lem4617988 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4617989 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term105 A s.
Proof. exact (@lem4617987 A s (@lem4617988 A s h1)). Qed.
Lemma lem4617990 {A : Type'} (s : A -> Prop) : (term105 A s) = ((term105 A s) = True).
Proof. exact (@lem7 (term105 A s)). Qed.
Lemma lem4617991 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term105 A s) = True.
Proof. exact (EQ_MP (@lem4617990 A s) (@lem4617989 A s h1)). Qed.
Lemma lem4617997 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem4617999 {B : Type'} (t : B -> Prop) : (@FINITE B t) = ((@FINITE B t) = True).
Proof. exact (@lem7 (@FINITE B t)). Qed.
Lemma lem4618004 {A B : Type'} (f : A -> B) (s : A -> Prop) : term106 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem4617964 A B f s h0). Qed.
Lemma lem4618005 {A B : Type'} (f : type323 A B) (s : type324 A B) : term107 A B f s.
Proof. exact (@lem4618004 (type1210 A B) (A -> B) f s). Qed.
Lemma lem4618006 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) : term108 A B k s t.
Proof. exact (@lem4618005 A B (term109 A B k) (term110 A B s t)). Qed.
Lemma lem4618008 {A : Type'} (s : A -> Prop) : term111 A s.
Proof. exact (fun h0 : @FINITE A s => @lem4617991 A s h0). Qed.
Lemma lem4618009 {A B : Type'} (s : type1210 A B) : term112 A B s.
Proof. exact (@lem4618008 (prod A B) s). Qed.
Lemma lem4618010 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term113 A B s t.
Proof. exact (@lem4618009 A B (@CROSS B A s t)). Qed.
Lemma lem4618012 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) : term114 _103774 _103776 s t.
Proof. exact (fun h0 : term89 _103774 _103776 s t => @lem4617979 _103774 _103776 s t h0). Qed.
Lemma lem4618013 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term114 A B s t.
Proof. exact (@lem4618012 A B s t). Qed.
Lemma lem4618017 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem4617997 A s) (@lem4617950 A s h1)). Qed.
Lemma lem4618018 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4618019 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term115 A s) = (and True).
Proof. exact (MK_COMB (@lem4618018) (@lem4618017 A s h1)). Qed.
Lemma lem4618021 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem4617999 B t) (@lem4617949 B t h1)). Qed.
Lemma lem4618022 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : (term89 A B s t) = (True /\ True).
Proof. exact (MK_COMB (@lem4618019 A s h1) (@lem4618021 B t h2)). Qed.
Lemma lem4618024 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4618025 : (True /\ True) = True.
Proof. exact (@lem4618024 True). Qed.
Lemma lem4618026 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : (term89 A B s t) = True.
Proof. exact (TRANS (@lem4618022 A B s t h1 h2) (@lem4618025)). Qed.
Lemma lem4618027 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : True = (term89 A B s t).
Proof. exact (SYM (@lem4618026 A B s t h1 h2)). Qed.
Lemma lem4618028 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : term89 A B s t.
Proof. exact (EQ_MP (@lem4618027 A B s t h1 h2) (@lem0)). Qed.
Lemma lem4618029 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : (term102 A B s t) = True.
Proof. exact (@lem4618013 A B s t (@lem4618028 A B s t h1 h2)). Qed.
Lemma lem4618030 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : True = (term102 A B s t).
Proof. exact (SYM (@lem4618029 A B s t h1 h2)). Qed.
Lemma lem4618031 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : term102 A B s t.
Proof. exact (EQ_MP (@lem4618030 A B s t h1 h2) (@lem0)). Qed.
Lemma lem4618032 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : (term116 A B s t) = True.
Proof. exact (@lem4618010 A B s t (@lem4618031 A B s t h1 h2)). Qed.
Lemma lem4618033 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : True = (term116 A B s t).
Proof. exact (SYM (@lem4618032 A B s t h1 h2)). Qed.
Lemma lem4618034 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : term116 A B s t.
Proof. exact (EQ_MP (@lem4618033 A B s t h1 h2) (@lem0)). Qed.
Lemma lem4618035 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : (term117 A B k s t) = True.
Proof. exact (@lem4618006 A B k s t (@lem4618034 A B s t h1 h2)). Qed.
Lemma lem4618036 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4618037 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : (term118 A B k s t) = (and True).
Proof. exact (MK_COMB (@lem4618036) (@lem4618035 A B k s t h1 h2)). Qed.
Lemma lem4618095 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term119 A B k s t) = (term119 A B k s t).
Proof. exact (eq_refl (term119 A B k s t)). Qed.
Lemma lem4618096 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : (term120 A B k s t) = (term121 A B k s t).
Proof. exact (MK_COMB (@lem4618037 A B k s t h1 h2) (@lem4618095 A B k s t)). Qed.
Lemma lem4618098 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4618099 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term121 A B k s t) = (term119 A B k s t).
Proof. exact (@lem4618098 (term119 A B k s t)). Qed.
Lemma lem4618157 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : (term120 A B k s t) = (term119 A B k s t).
Proof. exact (TRANS (@lem4618096 A B k s t h1 h2) (@lem4618099 A B k s t)). Qed.
Lemma lem4618158 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : (term119 A B k s t) = (term120 A B k s t).
Proof. exact (SYM (@lem4618157 A B k s t h1 h2)). Qed.
Lemma lem4618160 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term69 A s t).
Proof. exact (EQ_MP (@lem4617925 A s t) (@lem4617924 A s t)). Qed.
Lemma lem4618161 {A B : Type'} (s : type572 A B) (t : type572 A B) : (@SUBSET (A -> B) s t) = (term122 A B s t).
Proof. exact (@lem4618160 (A -> B) s t). Qed.
Lemma lem4618162 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term119 A B k s t) = (term123 A B k s t).
Proof. exact (@lem4618161 A B (term92 A B t k s) (term124 A B k s t)). Qed.
Lemma lem4618163 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term123 A B k s t) = (term119 A B k s t).
Proof. exact (SYM (@lem4618162 A B k s t)). Qed.
Lemma lem4618165 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) (f : _88905 -> _89106) : (term74 _88905 _89106 P f Q) = (term75 _88905 _89106 P Q f).
Proof. exact (EQ_MP (@lem4617919 _88905 _89106 P Q f) (@lem4617918 _88905 _89106 P Q f)). Qed.
Lemma lem4618166 {A B : Type'} (P : type572 A B) (Q : type572 A B) (f : type549 A B) : (term125 A B P f Q) = (term126 A B P Q f).
Proof. exact (@lem4618165 (A -> B) (A -> B) P Q f). Qed.
Lemma lem4618167 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term127 A B k s t) = (term128 A B k s t).
Proof. exact (@lem4618166 A B (term129 A B t k s) (term130 A B k s t) (term131 A B)). Qed.
Lemma lem4618168 {A B : Type'} (t : B -> Prop) (f : A -> B) (k : A -> B) (s : A -> Prop) : (term132 A B t k s f) = (term133 A B t f k s).
Proof. exact (eq_refl (term132 A B t k s f)). Qed.
Lemma lem4618169 {A B : Type'} (GEN_PVAR_178 : A -> B) : (@SETSPEC (A -> B) GEN_PVAR_178) = (@SETSPEC (A -> B) GEN_PVAR_178).
Proof. exact (eq_refl (@SETSPEC (A -> B) GEN_PVAR_178)). Qed.
Lemma lem4618170 {A B : Type'} (GEN_PVAR_178 : A -> B) (t : B -> Prop) (f : A -> B) (k : A -> B) (s : A -> Prop) : (term134 A B GEN_PVAR_178 t k s f) = (term135 A B GEN_PVAR_178 t f k s).
Proof. exact (MK_COMB (@lem4618169 A B GEN_PVAR_178) (@lem4618168 A B t f k s)). Qed.
Lemma lem4618171 {A B : Type'} (f : A -> B) : (term136 A B f) = f.
Proof. exact (eq_refl (term136 A B f)). Qed.
Lemma lem4618172 {A B : Type'} (GEN_PVAR_178 : A -> B) (t : B -> Prop) (k : A -> B) (s : A -> Prop) (f : A -> B) : (term137 A B GEN_PVAR_178 t k s f) = (term138 A B GEN_PVAR_178 t k s f).
Proof. exact (MK_COMB (@lem4618170 A B GEN_PVAR_178 t f k s) (@lem4618171 A B f)). Qed.
Lemma lem4618173 {A B : Type'} (GEN_PVAR_178 : A -> B) (t : B -> Prop) (k : A -> B) (s : A -> Prop) : (term139 A B GEN_PVAR_178 t k s) = (term140 A B GEN_PVAR_178 t k s).
Proof. exact (fun_ext (fun f : A -> B => @lem4618172 A B GEN_PVAR_178 t k s f)). Qed.
Lemma lem4618174 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem4618175 {A B : Type'} (GEN_PVAR_178 : A -> B) (t : B -> Prop) (k : A -> B) (s : A -> Prop) : (term141 A B GEN_PVAR_178 t k s) = (term142 A B GEN_PVAR_178 t k s).
Proof. exact (MK_COMB (@lem4618174 A B) (@lem4618173 A B GEN_PVAR_178 t k s)). Qed.
Lemma lem4618176 {A B : Type'} (t : B -> Prop) (k : A -> B) (s : A -> Prop) : (term143 A B t k s) = (term144 A B t k s).
Proof. exact (fun_ext (fun GEN_PVAR_178 : A -> B => @lem4618175 A B GEN_PVAR_178 t k s)). Qed.
Lemma lem4618177 {A B : Type'} : (@GSPEC (A -> B)) = (@GSPEC (A -> B)).
Proof. exact (eq_refl (@GSPEC (A -> B))). Qed.
Lemma lem4618178 {A B : Type'} (t : B -> Prop) (k : A -> B) (s : A -> Prop) : (term145 A B t k s) = (term92 A B t k s).
Proof. exact (MK_COMB (@lem4618177 A B) (@lem4618176 A B t k s)). Qed.
Lemma lem4618179 {A B : Type'} (x : A -> B) : (@IN (A -> B) x) = (@IN (A -> B) x).
Proof. exact (eq_refl (@IN (A -> B) x)). Qed.
Lemma lem4618180 {A B : Type'} (x : A -> B) (t : B -> Prop) (k : A -> B) (s : A -> Prop) : (term146 A B x t k s) = (term147 A B x t k s).
Proof. exact (MK_COMB (@lem4618179 A B x) (@lem4618178 A B t k s)). Qed.
Lemma lem4618181 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4618182 {A B : Type'} (x : A -> B) (t : B -> Prop) (k : A -> B) (s : A -> Prop) : (term148 A B x t k s) = (term149 A B x t k s).
Proof. exact (MK_COMB (@lem4618181) (@lem4618180 A B x t k s)). Qed.
Lemma lem4618183 {A B : Type'} (x : A -> B) (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term150 A B k s t x) = (term151 A B x k s t).
Proof. exact (eq_refl (term150 A B k s t x)). Qed.
Lemma lem4618184 {A B : Type'} (x : A -> B) (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term152 A B k s t x) = (term153 A B x k s t).
Proof. exact (MK_COMB (@lem4618182 A B x t k s) (@lem4618183 A B x k s t)). Qed.
Lemma lem4618185 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term154 A B k s t) = (term155 A B k s t).
Proof. exact (fun_ext (fun x : A -> B => @lem4618184 A B x k s t)). Qed.
Lemma lem4618186 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4618187 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term127 A B k s t) = (term123 A B k s t).
Proof. exact (MK_COMB (@lem4618186 A B) (@lem4618185 A B k s t)). Qed.
Lemma lem4618188 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4618189 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term156 A B k s t) = (term157 A B k s t).
Proof. exact (MK_COMB (@lem4618188) (@lem4618187 A B k s t)). Qed.
Lemma lem4618190 {A B : Type'} (t : B -> Prop) (f : A -> B) (k : A -> B) (s : A -> Prop) : (term132 A B t k s f) = (term133 A B t f k s).
Proof. exact (eq_refl (term132 A B t k s f)). Qed.
Lemma lem4618191 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4618192 {A B : Type'} (t : B -> Prop) (f : A -> B) (k : A -> B) (s : A -> Prop) : (term158 A B t k s f) = (term159 A B t f k s).
Proof. exact (MK_COMB (@lem4618191) (@lem4618190 A B t f k s)). Qed.
Lemma lem4618193 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term160 A B k s t f) = (term161 A B f k s t).
Proof. exact (eq_refl (term160 A B k s t f)). Qed.
Lemma lem4618194 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term162 A B k s t f) = (term163 A B f k s t).
Proof. exact (MK_COMB (@lem4618192 A B t f k s) (@lem4618193 A B f k s t)). Qed.
Lemma lem4618195 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term164 A B k s t) = (term165 A B k s t).
Proof. exact (fun_ext (fun f : A -> B => @lem4618194 A B f k s t)). Qed.
Lemma lem4618196 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4618197 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term128 A B k s t) = (term166 A B k s t).
Proof. exact (MK_COMB (@lem4618196 A B) (@lem4618195 A B k s t)). Qed.
Lemma lem4618198 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) : ((term127 A B k s t) = (term128 A B k s t)) = ((term123 A B k s t) = (term166 A B k s t)).
Proof. exact (MK_COMB (@lem4618189 A B k s t) (@lem4618197 A B k s t)). Qed.
Lemma lem4618199 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term123 A B k s t) = (term166 A B k s t).
Proof. exact (EQ_MP (@lem4618198 A B k s t) (@lem4618167 A B k s t)). Qed.
Lemma lem4618215 {A B : Type'} (f : A -> B) (y : A) : (term167 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4618216 {A B : Type'} (f : type549 A B) (y : A -> B) : (term168 A B f y) = (f y).
Proof. exact (@lem4618215 (A -> B) (A -> B) f y). Qed.
Lemma lem4618217 {A B : Type'} (f : A -> B) : (term169 A B f) = (term136 A B f).
Proof. exact (@lem4618216 A B (term131 A B) f). Qed.
Lemma lem4618218 {A B : Type'} (f : A -> B) : (term136 A B f) = f.
Proof. exact (eq_refl (term136 A B f)). Qed.
Lemma lem4618219 {A B : Type'} : (term170 A B) = (term131 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4618218 A B f)). Qed.
Lemma lem4618220 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4618221 {A B : Type'} (f : A -> B) : (term169 A B f) = (term136 A B f).
Proof. exact (MK_COMB (@lem4618219 A B) (@lem4618220 A B f)). Qed.
Lemma lem4618222 {A B : Type'} : (@eq (A -> B)) = (@eq (A -> B)).
Proof. exact (eq_refl (@eq (A -> B))). Qed.
Lemma lem4618223 {A B : Type'} (f : A -> B) : (term171 A B f) = (term172 A B f).
Proof. exact (MK_COMB (@lem4618222 A B) (@lem4618221 A B f)). Qed.
Lemma lem4618224 {A B : Type'} (f : A -> B) : (term136 A B f) = f.
Proof. exact (eq_refl (term136 A B f)). Qed.
Lemma lem4618225 {A B : Type'} (f : A -> B) : ((term169 A B f) = (term136 A B f)) = ((term136 A B f) = f).
Proof. exact (MK_COMB (@lem4618223 A B f) (@lem4618224 A B f)). Qed.
Lemma lem4618226 {A B : Type'} (f : A -> B) : (term136 A B f) = f.
Proof. exact (EQ_MP (@lem4618225 A B f) (@lem4618217 A B f)). Qed.
Lemma lem4618227 {A B : Type'} : (@IN (A -> B)) = (@IN (A -> B)).
Proof. exact (eq_refl (@IN (A -> B))). Qed.
Lemma lem4618228 {A B : Type'} (f : A -> B) : (term173 A B f) = (@IN (A -> B) f).
Proof. exact (MK_COMB (@lem4618227 A B) (@lem4618226 A B f)). Qed.
Lemma lem4618237 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term124 A B k s t) = (term124 A B k s t).
Proof. exact (eq_refl (term124 A B k s t)). Qed.
Lemma lem4618238 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term161 A B f k s t) = (term151 A B f k s t).
Proof. exact (MK_COMB (@lem4618228 A B f) (@lem4618237 A B k s t)). Qed.
Lemma lem4618239 {A B : Type'} (t : B -> Prop) (f : A -> B) (k : A -> B) (s : A -> Prop) : (term159 A B t f k s) = (term159 A B t f k s).
Proof. exact (eq_refl (term159 A B t f k s)). Qed.
Lemma lem4618240 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term163 A B f k s t) = (term174 A B f k s t).
Proof. exact (MK_COMB (@lem4618239 A B t f k s) (@lem4618238 A B f k s t)). Qed.
Lemma lem4618243 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term165 A B k s t) = (term175 A B k s t).
Proof. exact (fun_ext (fun f : A -> B => @lem4618240 A B f k s t)). Qed.
Lemma lem4618244 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4618245 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term166 A B k s t) = (term176 A B k s t).
Proof. exact (MK_COMB (@lem4618244 A B) (@lem4618243 A B k s t)). Qed.
Lemma lem4618250 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term123 A B k s t) = (term176 A B k s t).
Proof. exact (TRANS (@lem4618199 A B k s t) (@lem4618245 A B k s t)). Qed.
Lemma lem4618251 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term176 A B k s t) = (term123 A B k s t).
Proof. exact (SYM (@lem4618250 A B k s t)). Qed.
Lemma lem4618252 {A B : Type'} (t : B -> Prop) (f : A -> B) (k : A -> B) (s : A -> Prop) (h1 : term133 A B t f k s) : term133 A B t f k s.
Proof. exact (h1). Qed.
Lemma lem4618253 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (h1 : term177 A B f k s) : term177 A B f k s.
Proof. exact (h1). Qed.
Lemma lem4618254 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term178 A B f s t) : term178 A B f s t.
Proof. exact (h1). Qed.
Lemma lem4618256 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term46 A B y f s) = (term47 A B y f s).
Proof. exact (EQ_MP (@lem4617889 A B y f s) (@lem4617888 A B y s f)). Qed.
Lemma lem4618257 {A B : Type'} (y : A -> B) (f : type323 A B) (s : type324 A B) : (term179 A B y f s) = (term180 A B y f s).
Proof. exact (@lem4618256 (type1210 A B) (A -> B) y f s). Qed.
Lemma lem4618258 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term151 A B f k s t) = (term181 A B f k s t).
Proof. exact (@lem4618257 A B f (term109 A B k) (term110 A B s t)). Qed.
Lemma lem4618268 {A B : Type'} (f : A -> B) (y : A) : (term167 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4618269 {A B : Type'} (f : type323 A B) (y : type1210 A B) : (term182 A B f y) = (f y).
Proof. exact (@lem4618268 (type1210 A B) (A -> B) f y). Qed.
Lemma lem4618270 {A B : Type'} (k : A -> B) (x : type1210 A B) : (term183 A B k x) = (term184 A B k x).
Proof. exact (@lem4618269 A B (term109 A B k) x). Qed.
Lemma lem4618271 {A B : Type'} (u : type1210 A B) (k : A -> B) : (term184 A B k u) = (term185 A B u k).
Proof. exact (eq_refl (term184 A B k u)). Qed.
Lemma lem4618272 {A B : Type'} (k : A -> B) : (term186 A B k) = (term109 A B k).
Proof. exact (fun_ext (fun u : type1210 A B => @lem4618271 A B u k)). Qed.
Lemma lem4618273 {A B : Type'} (x : type1210 A B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4618274 {A B : Type'} (k : A -> B) (x : type1210 A B) : (term183 A B k x) = (term184 A B k x).
Proof. exact (MK_COMB (@lem4618272 A B k) (@lem4618273 A B x)). Qed.
Lemma lem4618275 {A B : Type'} : (@eq (A -> B)) = (@eq (A -> B)).
Proof. exact (eq_refl (@eq (A -> B))). Qed.
Lemma lem4618276 {A B : Type'} (k : A -> B) (x : type1210 A B) : (term187 A B k x) = (term188 A B k x).
Proof. exact (MK_COMB (@lem4618275 A B) (@lem4618274 A B k x)). Qed.
Lemma lem4618277 {A B : Type'} (x : type1210 A B) (k : A -> B) : (term184 A B k x) = (term185 A B x k).
Proof. exact (eq_refl (term184 A B k x)). Qed.
Lemma lem4618278 {A B : Type'} (x : type1210 A B) (k : A -> B) : ((term183 A B k x) = (term184 A B k x)) = ((term184 A B k x) = (term185 A B x k)).
Proof. exact (MK_COMB (@lem4618276 A B k x) (@lem4618277 A B x k)). Qed.
Lemma lem4618279 {A B : Type'} (x : type1210 A B) (k : A -> B) : (term184 A B k x) = (term185 A B x k).
Proof. exact (EQ_MP (@lem4618278 A B x k) (@lem4618270 A B k x)). Qed.
Lemma lem4618284 {A B : Type'} (f : A -> B) : (@eq (A -> B) f) = (@eq (A -> B) f).
Proof. exact (eq_refl (@eq (A -> B) f)). Qed.
Lemma lem4618285 {A B : Type'} (f : A -> B) (x : type1210 A B) (k : A -> B) : (f = (term184 A B k x)) = (f = (term185 A B x k)).
Proof. exact (MK_COMB (@lem4618284 A B f) (@lem4618279 A B x k)). Qed.
Lemma lem4618288 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4618289 {A B : Type'} (f : A -> B) (x : type1210 A B) (k : A -> B) : (term189 A B f k x) = (term190 A B f x k).
Proof. exact (MK_COMB (@lem4618288) (@lem4618285 A B f x k)). Qed.
Lemma lem4618291 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term40 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4617873 _83095 p x) (@lem4617872 _83095 p x)). Qed.
Lemma lem4618292 {A B : Type'} (p : type324 A B) (x : type1210 A B) : (term191 A B x p) = (p x).
Proof. exact (@lem4618291 (type1210 A B) p x). Qed.
Lemma lem4618293 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : type1210 A B) : (term192 A B x s t) = (term193 A B s t x).
Proof. exact (@lem4618292 A B (term194 A B s t) x). Qed.
Lemma lem4618294 {A B : Type'} (u : type1210 A B) (s : A -> Prop) (t : B -> Prop) : (term193 A B s t u) = (term195 A B u s t).
Proof. exact (eq_refl (term193 A B s t u)). Qed.
Lemma lem4618295 {A B : Type'} (GEN_PVAR_176 : type1210 A B) : (@SETSPEC ((prod A B) -> Prop) GEN_PVAR_176) = (@SETSPEC ((prod A B) -> Prop) GEN_PVAR_176).
Proof. exact (eq_refl (@SETSPEC ((prod A B) -> Prop) GEN_PVAR_176)). Qed.
Lemma lem4618296 {A B : Type'} (GEN_PVAR_176 : type1210 A B) (u : type1210 A B) (s : A -> Prop) (t : B -> Prop) : (term196 A B GEN_PVAR_176 s t u) = (term197 A B GEN_PVAR_176 u s t).
Proof. exact (MK_COMB (@lem4618295 A B GEN_PVAR_176) (@lem4618294 A B u s t)). Qed.
Lemma lem4618297 {A B : Type'} (u : type1210 A B) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem4618298 {A B : Type'} (GEN_PVAR_176 : type1210 A B) (s : A -> Prop) (t : B -> Prop) (u : type1210 A B) : (term198 A B GEN_PVAR_176 s t u) = (term199 A B GEN_PVAR_176 s t u).
Proof. exact (MK_COMB (@lem4618296 A B GEN_PVAR_176 u s t) (@lem4618297 A B u)). Qed.
Lemma lem4618299 {A B : Type'} (GEN_PVAR_176 : type1210 A B) (s : A -> Prop) (t : B -> Prop) : (term200 A B GEN_PVAR_176 s t) = (term201 A B GEN_PVAR_176 s t).
Proof. exact (fun_ext (fun u : type1210 A B => @lem4618298 A B GEN_PVAR_176 s t u)). Qed.
Lemma lem4618300 {A B : Type'} : (@ex ((prod A B) -> Prop)) = (@ex ((prod A B) -> Prop)).
Proof. exact (eq_refl (@ex ((prod A B) -> Prop))). Qed.
Lemma lem4618301 {A B : Type'} (GEN_PVAR_176 : type1210 A B) (s : A -> Prop) (t : B -> Prop) : (term202 A B GEN_PVAR_176 s t) = (term203 A B GEN_PVAR_176 s t).
Proof. exact (MK_COMB (@lem4618300 A B) (@lem4618299 A B GEN_PVAR_176 s t)). Qed.
Lemma lem4618302 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term204 A B s t) = (term205 A B s t).
Proof. exact (fun_ext (fun GEN_PVAR_176 : type1210 A B => @lem4618301 A B GEN_PVAR_176 s t)). Qed.
Lemma lem4618303 {A B : Type'} : (@GSPEC ((prod A B) -> Prop)) = (@GSPEC ((prod A B) -> Prop)).
Proof. exact (eq_refl (@GSPEC ((prod A B) -> Prop))). Qed.
Lemma lem4618304 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term206 A B s t) = (term110 A B s t).
Proof. exact (MK_COMB (@lem4618303 A B) (@lem4618302 A B s t)). Qed.
Lemma lem4618305 {A B : Type'} (x : type1210 A B) : (@IN ((prod A B) -> Prop) x) = (@IN ((prod A B) -> Prop) x).
Proof. exact (eq_refl (@IN ((prod A B) -> Prop) x)). Qed.
Lemma lem4618306 {A B : Type'} (x : type1210 A B) (s : A -> Prop) (t : B -> Prop) : (term192 A B x s t) = (term207 A B x s t).
Proof. exact (MK_COMB (@lem4618305 A B x) (@lem4618304 A B s t)). Qed.
Lemma lem4618307 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4618308 {A B : Type'} (x : type1210 A B) (s : A -> Prop) (t : B -> Prop) : (term208 A B x s t) = (term209 A B x s t).
Proof. exact (MK_COMB (@lem4618307) (@lem4618306 A B x s t)). Qed.
Lemma lem4618309 {A B : Type'} (x : type1210 A B) (s : A -> Prop) (t : B -> Prop) : (term193 A B s t x) = (term195 A B x s t).
Proof. exact (eq_refl (term193 A B s t x)). Qed.
Lemma lem4618310 {A B : Type'} (x : type1210 A B) (s : A -> Prop) (t : B -> Prop) : ((term192 A B x s t) = (term193 A B s t x)) = ((term207 A B x s t) = (term195 A B x s t)).
Proof. exact (MK_COMB (@lem4618308 A B x s t) (@lem4618309 A B x s t)). Qed.
Lemma lem4618311 {A B : Type'} (x : type1210 A B) (s : A -> Prop) (t : B -> Prop) : (term207 A B x s t) = (term195 A B x s t).
Proof. exact (EQ_MP (@lem4618310 A B x s t) (@lem4618293 A B s t x)). Qed.
Lemma lem4618312 {A B : Type'} (f : A -> B) (k : A -> B) (x : type1210 A B) (s : A -> Prop) (t : B -> Prop) : (term210 A B f k x s t) = (term211 A B f k x s t).
Proof. exact (MK_COMB (@lem4618289 A B f x k) (@lem4618311 A B x s t)). Qed.
Lemma lem4618315 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term212 A B f k s t) = (term213 A B f k s t).
Proof. exact (fun_ext (fun x : type1210 A B => @lem4618312 A B f k x s t)). Qed.
Lemma lem4618316 {A B : Type'} : (@ex ((prod A B) -> Prop)) = (@ex ((prod A B) -> Prop)).
Proof. exact (eq_refl (@ex ((prod A B) -> Prop))). Qed.
Lemma lem4618317 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term181 A B f k s t) = (term214 A B f k s t).
Proof. exact (MK_COMB (@lem4618316 A B) (@lem4618315 A B f k s t)). Qed.
Lemma lem4618322 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term151 A B f k s t) = (term214 A B f k s t).
Proof. exact (TRANS (@lem4618258 A B f k s t) (@lem4618317 A B f k s t)). Qed.
Lemma lem4618323 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term214 A B f k s t) = (term151 A B f k s t).
Proof. exact (SYM (@lem4618322 A B f k s t)). Qed.
Lemma lem4618425 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term69 A s t).
Proof. exact (EQ_MP (@lem4617842 A s t) (@lem4617841 A s t)). Qed.
Lemma lem4618426 {A B : Type'} (s : type1210 A B) (t : type1210 A B) : (@SUBSET (prod A B) s t) = (term215 A B s t).
Proof. exact (@lem4618425 (prod A B) s t). Qed.
Lemma lem4618427 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term216 A B f k s t) = (term217 A B f k s t).
Proof. exact (@lem4618426 A B (term218 A B f k) (@CROSS B A s t)). Qed.
Lemma lem4618429 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term64 _87967 _87968 f s P) = (term65 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem4617836 _87967 _87968 s P f) (@lem4617835 _87967 _87968 P f s)). Qed.
Lemma lem4618430 {A B : Type'} (s : A -> Prop) (P : type1210 A B) (f : type1428 A B) : (term219 A B f s P) = (term220 A B s P f).
Proof. exact (@lem4618429 (prod A B) A s P f). Qed.
Lemma lem4618431 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term221 A B f k s t) = (term222 A B k s t f).
Proof. exact (@lem4618430 A B (term223 A B f k) (term224 A B s t) (term225 A B f)). Qed.
Lemma lem4618432 {A B : Type'} (x : prod A B) (s : A -> Prop) (t : B -> Prop) : (term226 A B s t x) = (term227 A B x s t).
Proof. exact (eq_refl (term226 A B s t x)). Qed.
Lemma lem4618433 {A B : Type'} (x : prod A B) (f : A -> B) (k : A -> B) : (term228 A B x f k) = (term228 A B x f k).
Proof. exact (eq_refl (term228 A B x f k)). Qed.
Lemma lem4618434 {A B : Type'} (f : A -> B) (k : A -> B) (x : prod A B) (s : A -> Prop) (t : B -> Prop) : (term229 A B f k s t x) = (term230 A B f k x s t).
Proof. exact (MK_COMB (@lem4618433 A B x f k) (@lem4618432 A B x s t)). Qed.
Lemma lem4618435 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term231 A B f k s t) = (term232 A B f k s t).
Proof. exact (fun_ext (fun x : prod A B => @lem4618434 A B f k x s t)). Qed.
Lemma lem4618436 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4618437 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term221 A B f k s t) = (term217 A B f k s t).
Proof. exact (MK_COMB (@lem4618436 A B) (@lem4618435 A B f k s t)). Qed.
Lemma lem4618438 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4618439 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term233 A B f k s t) = (term234 A B f k s t).
Proof. exact (MK_COMB (@lem4618438) (@lem4618437 A B f k s t)). Qed.
Lemma lem4618440 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (t : B -> Prop) : (term235 A B s t f x) = (term236 A B f x s t).
Proof. exact (eq_refl (term235 A B s t f x)). Qed.
Lemma lem4618441 {A B : Type'} (x : A) (f : A -> B) (k : A -> B) : (term237 A B x f k) = (term237 A B x f k).
Proof. exact (eq_refl (term237 A B x f k)). Qed.
Lemma lem4618442 {A B : Type'} (k : A -> B) (f : A -> B) (x : A) (s : A -> Prop) (t : B -> Prop) : (term238 A B k s t f x) = (term239 A B k f x s t).
Proof. exact (MK_COMB (@lem4618441 A B x f k) (@lem4618440 A B f x s t)). Qed.
Lemma lem4618443 {A B : Type'} (k : A -> B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term240 A B k s t f) = (term241 A B k f s t).
Proof. exact (fun_ext (fun x : A => @lem4618442 A B k f x s t)). Qed.
Lemma lem4618444 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4618445 {A B : Type'} (k : A -> B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term222 A B k s t f) = (term242 A B k f s t).
Proof. exact (MK_COMB (@lem4618444 A) (@lem4618443 A B k f s t)). Qed.
Lemma lem4618446 {A B : Type'} (k : A -> B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : ((term221 A B f k s t) = (term222 A B k s t f)) = ((term217 A B f k s t) = (term242 A B k f s t)).
Proof. exact (MK_COMB (@lem4618439 A B f k s t) (@lem4618445 A B k f s t)). Qed.
Lemma lem4618447 {A B : Type'} (k : A -> B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term217 A B f k s t) = (term242 A B k f s t).
Proof. exact (EQ_MP (@lem4618446 A B k f s t) (@lem4618431 A B k s t f)). Qed.
Lemma lem4618452 {A B : Type'} (k : A -> B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term216 A B f k s t) = (term242 A B k f s t).
Proof. exact (TRANS (@lem4618427 A B f k s t) (@lem4618447 A B k f s t)). Qed.
Lemma lem4618456 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term40 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4617823 _83095 p x) (@lem4617822 _83095 p x)). Qed.
Lemma lem4618457 {A : Type'} (p : A -> Prop) (x : A) : (term40 A x p) = (p x).
Proof. exact (@lem4618456 A p x). Qed.
Lemma lem4618458 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term243 A B x f k) = (term244 A B f k x).
Proof. exact (@lem4618457 A (term245 A B f k) x). Qed.
Lemma lem4618459 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term244 A B f k x) = (term2 A B f k x).
Proof. exact (eq_refl (term244 A B f k x)). Qed.
Lemma lem4618460 {A : Type'} (GEN_PVAR_175 : A) : (@SETSPEC A GEN_PVAR_175) = (@SETSPEC A GEN_PVAR_175).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_175)). Qed.
Lemma lem4618461 {A B : Type'} (GEN_PVAR_175 : A) (f : A -> B) (k : A -> B) (x : A) : (term246 A B GEN_PVAR_175 f k x) = (term247 A B GEN_PVAR_175 f k x).
Proof. exact (MK_COMB (@lem4618460 A GEN_PVAR_175) (@lem4618459 A B f k x)). Qed.
Lemma lem4618462 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4618463 {A B : Type'} (GEN_PVAR_175 : A) (f : A -> B) (k : A -> B) (x : A) : (term248 A B GEN_PVAR_175 f k x) = (term249 A B GEN_PVAR_175 f k x).
Proof. exact (MK_COMB (@lem4618461 A B GEN_PVAR_175 f k x) (@lem4618462 A x)). Qed.
Lemma lem4618464 {A B : Type'} (GEN_PVAR_175 : A) (f : A -> B) (k : A -> B) : (term250 A B GEN_PVAR_175 f k) = (term251 A B GEN_PVAR_175 f k).
Proof. exact (fun_ext (fun x : A => @lem4618463 A B GEN_PVAR_175 f k x)). Qed.
Lemma lem4618465 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4618466 {A B : Type'} (GEN_PVAR_175 : A) (f : A -> B) (k : A -> B) : (term252 A B GEN_PVAR_175 f k) = (term253 A B GEN_PVAR_175 f k).
Proof. exact (MK_COMB (@lem4618465 A) (@lem4618464 A B GEN_PVAR_175 f k)). Qed.
Lemma lem4618467 {A B : Type'} (f : A -> B) (k : A -> B) : (term254 A B f k) = (term255 A B f k).
Proof. exact (fun_ext (fun GEN_PVAR_175 : A => @lem4618466 A B GEN_PVAR_175 f k)). Qed.
Lemma lem4618468 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4618469 {A B : Type'} (f : A -> B) (k : A -> B) : (term256 A B f k) = (term223 A B f k).
Proof. exact (MK_COMB (@lem4618468 A) (@lem4618467 A B f k)). Qed.
Lemma lem4618470 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4618471 {A B : Type'} (x : A) (f : A -> B) (k : A -> B) : (term243 A B x f k) = (term257 A B x f k).
Proof. exact (MK_COMB (@lem4618470 A x) (@lem4618469 A B f k)). Qed.
Lemma lem4618472 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4618473 {A B : Type'} (x : A) (f : A -> B) (k : A -> B) : (term258 A B x f k) = (term259 A B x f k).
Proof. exact (MK_COMB (@lem4618472) (@lem4618471 A B x f k)). Qed.
Lemma lem4618474 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term244 A B f k x) = (term2 A B f k x).
Proof. exact (eq_refl (term244 A B f k x)). Qed.
Lemma lem4618475 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : ((term243 A B x f k) = (term244 A B f k x)) = ((term257 A B x f k) = (term2 A B f k x)).
Proof. exact (MK_COMB (@lem4618473 A B x f k) (@lem4618474 A B f k x)). Qed.
Lemma lem4618476 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term257 A B x f k) = (term2 A B f k x).
Proof. exact (EQ_MP (@lem4618475 A B f k x) (@lem4618458 A B f k x)). Qed.
Lemma lem4618479 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4618480 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term237 A B x f k) = (term260 A B f k x).
Proof. exact (MK_COMB (@lem4618479) (@lem4618476 A B f k x)). Qed.
Lemma lem4618482 {A B : Type'} (f : A -> B) (y : A) : (term167 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4618483 {A B : Type'} (f : type1428 A B) (y : A) : (term261 A B f y) = (f y).
Proof. exact (@lem4618482 A (prod A B) f y). Qed.
Lemma lem4618484 {A B : Type'} (f : A -> B) (x : A) : (term262 A B f x) = (term263 A B f x).
Proof. exact (@lem4618483 A B (term225 A B f) x). Qed.
Lemma lem4618485 {A B : Type'} (f : A -> B) (x : A) : (term263 A B f x) = (term264 A B f x).
Proof. exact (eq_refl (term263 A B f x)). Qed.
Lemma lem4618486 {A B : Type'} (f : A -> B) : (term265 A B f) = (term225 A B f).
Proof. exact (fun_ext (fun x : A => @lem4618485 A B f x)). Qed.
Lemma lem4618487 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4618488 {A B : Type'} (f : A -> B) (x : A) : (term262 A B f x) = (term263 A B f x).
Proof. exact (MK_COMB (@lem4618486 A B f) (@lem4618487 A x)). Qed.
Lemma lem4618489 {A B : Type'} : (@eq (prod A B)) = (@eq (prod A B)).
Proof. exact (eq_refl (@eq (prod A B))). Qed.
Lemma lem4618490 {A B : Type'} (f : A -> B) (x : A) : (term266 A B f x) = (term267 A B f x).
Proof. exact (MK_COMB (@lem4618489 A B) (@lem4618488 A B f x)). Qed.
Lemma lem4618491 {A B : Type'} (f : A -> B) (x : A) : (term263 A B f x) = (term264 A B f x).
Proof. exact (eq_refl (term263 A B f x)). Qed.
Lemma lem4618492 {A B : Type'} (f : A -> B) (x : A) : ((term262 A B f x) = (term263 A B f x)) = ((term263 A B f x) = (term264 A B f x)).
Proof. exact (MK_COMB (@lem4618490 A B f x) (@lem4618491 A B f x)). Qed.
Lemma lem4618493 {A B : Type'} (f : A -> B) (x : A) : (term263 A B f x) = (term264 A B f x).
Proof. exact (EQ_MP (@lem4618492 A B f x) (@lem4618484 A B f x)). Qed.
Lemma lem4618494 {A B : Type'} : (@IN (prod A B)) = (@IN (prod A B)).
Proof. exact (eq_refl (@IN (prod A B))). Qed.
Lemma lem4618495 {A B : Type'} (f : A -> B) (x : A) : (term268 A B f x) = (term269 A B f x).
Proof. exact (MK_COMB (@lem4618494 A B) (@lem4618493 A B f x)). Qed.
Lemma lem4618496 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (@CROSS B A s t) = (@CROSS B A s t).
Proof. exact (eq_refl (@CROSS B A s t)). Qed.
Lemma lem4618497 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (t : B -> Prop) : (term236 A B f x s t) = (term270 A B f x s t).
Proof. exact (MK_COMB (@lem4618495 A B f x) (@lem4618496 A B s t)). Qed.
Lemma lem4618499 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term59 _103718 _103721 x y s t) = (term60 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4617792 _103718 _103721 x s y t) (@lem4617791 _103718 _103721 x s y t)). Qed.
Lemma lem4618500 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) : (term59 A B x y s t) = (term60 A B x s y t).
Proof. exact (@lem4618499 A B x s y t). Qed.
Lemma lem4618501 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term270 A B f x s t) = (term271 A B s f x t).
Proof. exact (@lem4618500 A B x s (f x) t). Qed.
Lemma lem4618504 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term236 A B f x s t) = (term271 A B s f x t).
Proof. exact (TRANS (@lem4618497 A B f x s t) (@lem4618501 A B s f x t)). Qed.
Lemma lem4618505 {A B : Type'} (k : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term239 A B k f x s t) = (term272 A B k s f x t).
Proof. exact (MK_COMB (@lem4618480 A B f k x) (@lem4618504 A B s f x t)). Qed.
Lemma lem4618508 {A B : Type'} (k : A -> B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term241 A B k f s t) = (term273 A B k s f t).
Proof. exact (fun_ext (fun x : A => @lem4618505 A B k s f x t)). Qed.
Lemma lem4618509 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4618510 {A B : Type'} (k : A -> B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term242 A B k f s t) = (term274 A B k s f t).
Proof. exact (MK_COMB (@lem4618509 A) (@lem4618508 A B k s f t)). Qed.
Lemma lem4618515 {A B : Type'} (k : A -> B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term216 A B f k s t) = (term274 A B k s f t).
Proof. exact (TRANS (@lem4618452 A B k f s t) (@lem4618510 A B k s f t)). Qed.
Lemma lem4618516 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (t : B -> Prop) : (term274 A B k s f t) = (term216 A B f k s t).
Proof. exact (SYM (@lem4618515 A B k s f t)). Qed.
Lemma lem4618517 (t1 : Prop) : term275 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4618518 (t1 : Prop) : (term275 t1) = (term276 t1).
Proof. exact (eq_refl (term275 t1)). Qed.
Lemma lem4618519 (t1 : Prop) : term276 t1.
Proof. exact (EQ_MP (@lem4618518 t1) (@lem4618517 t1)). Qed.
Lemma lem4618520 (t1 : Prop) (t2 : Prop) : term277 t1 t2.
Proof. exact (@lem4618519 t1 t2). Qed.
Lemma lem4618521 (t1 : Prop) (t2 : Prop) : (term277 t1 t2) = (term278 t1 t2).
Proof. exact (eq_refl (term277 t1 t2)). Qed.
Lemma lem4618522 (t1 : Prop) (t2 : Prop) : term278 t1 t2.
Proof. exact (EQ_MP (@lem4618521 t1 t2) (@lem4618520 t1 t2)). Qed.
Lemma lem4618523 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term279 t1 t2 t3.
Proof. exact (@lem4618522 t1 t2 t3). Qed.
Lemma lem4618524 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term279 t1 t2 t3) = ((term280 t1 t2 t3) = (term281 t1 t2 t3)).
Proof. exact (eq_refl (term279 t1 t2 t3)). Qed.
Lemma lem4618525 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term280 t1 t2 t3) = (term281 t1 t2 t3).
Proof. exact (EQ_MP (@lem4618524 t1 t2 t3) (@lem4618523 t1 t2 t3)). Qed.
Lemma lem4618526 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term281 t1 t2 t3) = (term280 t1 t2 t3).
Proof. exact (SYM (@lem4618525 t1 t2 t3)). Qed.
Lemma lem4618527 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : term282 A B t s.
Proof. exact (conj (@lem4617949 B t h2) (@lem4617950 A s h1)). Qed.
Lemma lem4618528 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term178 A B f s t) : term283 A B f t s.
Proof. exact (conj (@lem4618254 A B f s t h3) (@lem4618527 A B s t h1 h2)). Qed.
Lemma lem4618529 {A B : Type'} (k : A -> B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term177 A B f k s) (h4 : term178 A B f s t) : term284 A B k f t s.
Proof. exact (conj (@lem4618253 A B f k s h3) (@lem4618528 A B f s t h1 h2 h4)). Qed.
Lemma lem4618535 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term69 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4618536 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term69 A s t).
Proof. exact (@lem4618535 A s t). Qed.
Lemma lem4618537 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) : (term177 A B f k s) = (term285 A B f k s).
Proof. exact (@lem4618536 A (term223 A B f k) s). Qed.
Lemma lem4618552 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4618553 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) : (term286 A B f k s) = (term287 A B f k s).
Proof. exact (MK_COMB (@lem4618552) (@lem4618537 A B f k s)). Qed.
Lemma lem4618557 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term69 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4618558 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term69 B s t).
Proof. exact (@lem4618557 B s t). Qed.
Lemma lem4618559 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term178 A B f s t) = (term288 A B f s t).
Proof. exact (@lem4618558 B (@IMAGE A B f s) t). Qed.
Lemma lem4618566 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4618567 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term289 A B f s t) = (term290 A B f s t).
Proof. exact (MK_COMB (@lem4618566) (@lem4618559 A B f s t)). Qed.
Lemma lem4618570 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term282 A B t s) = (term282 A B t s).
Proof. exact (eq_refl (term282 A B t s)). Qed.
Lemma lem4618571 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term283 A B f t s) = (term291 A B f t s).
Proof. exact (MK_COMB (@lem4618567 A B f s t) (@lem4618570 A B t s)). Qed.
Lemma lem4618574 {A B : Type'} (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term284 A B k f t s) = (term292 A B k f t s).
Proof. exact (MK_COMB (@lem4618553 A B f k s) (@lem4618571 A B f t s)). Qed.
Lemma lem4618577 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4618578 {A B : Type'} (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term293 A B k f t s) = (term294 A B k f t s).
Proof. exact (MK_COMB (@lem4618577) (@lem4618574 A B k f t s)). Qed.
Lemma lem4618591 {A B : Type'} (k : A -> B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term274 A B k s f t) = (term274 A B k s f t).
Proof. exact (eq_refl (term274 A B k s f t)). Qed.
Lemma lem4618592 {A B : Type'} (k : A -> B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term295 A B k s f t) = (term296 A B k s f t).
Proof. exact (MK_COMB (@lem4618578 A B k f t s) (@lem4618591 A B k s f t)). Qed.
Lemma lem4618595 {A B : Type'} (k : A -> B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term296 A B k s f t) = (term295 A B k s f t).
Proof. exact (SYM (@lem4618592 A B k s f t)). Qed.
Lemma lem4618607 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term40 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4618608 {A : Type'} (p : A -> Prop) (x : A) : (term40 A x p) = (p x).
Proof. exact (@lem4618607 A p x). Qed.
Lemma lem4618609 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term243 A B x f k) = (term244 A B f k x).
Proof. exact (@lem4618608 A (term245 A B f k) x). Qed.
Lemma lem4618610 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term244 A B f k x) = (term2 A B f k x).
Proof. exact (eq_refl (term244 A B f k x)). Qed.
Lemma lem4618611 {A : Type'} (GEN_PVAR_177 : A) : (@SETSPEC A GEN_PVAR_177) = (@SETSPEC A GEN_PVAR_177).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_177)). Qed.
Lemma lem4618612 {A B : Type'} (GEN_PVAR_177 : A) (f : A -> B) (k : A -> B) (x : A) : (term246 A B GEN_PVAR_177 f k x) = (term247 A B GEN_PVAR_177 f k x).
Proof. exact (MK_COMB (@lem4618611 A GEN_PVAR_177) (@lem4618610 A B f k x)). Qed.
Lemma lem4618613 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4618614 {A B : Type'} (GEN_PVAR_177 : A) (f : A -> B) (k : A -> B) (x : A) : (term248 A B GEN_PVAR_177 f k x) = (term249 A B GEN_PVAR_177 f k x).
Proof. exact (MK_COMB (@lem4618612 A B GEN_PVAR_177 f k x) (@lem4618613 A x)). Qed.
Lemma lem4618615 {A B : Type'} (GEN_PVAR_177 : A) (f : A -> B) (k : A -> B) : (term250 A B GEN_PVAR_177 f k) = (term251 A B GEN_PVAR_177 f k).
Proof. exact (fun_ext (fun x : A => @lem4618614 A B GEN_PVAR_177 f k x)). Qed.
Lemma lem4618616 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4618617 {A B : Type'} (GEN_PVAR_177 : A) (f : A -> B) (k : A -> B) : (term252 A B GEN_PVAR_177 f k) = (term253 A B GEN_PVAR_177 f k).
Proof. exact (MK_COMB (@lem4618616 A) (@lem4618615 A B GEN_PVAR_177 f k)). Qed.
Lemma lem4618618 {A B : Type'} (f : A -> B) (k : A -> B) : (term254 A B f k) = (term255 A B f k).
Proof. exact (fun_ext (fun GEN_PVAR_177 : A => @lem4618617 A B GEN_PVAR_177 f k)). Qed.
Lemma lem4618619 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4618620 {A B : Type'} (f : A -> B) (k : A -> B) : (term256 A B f k) = (term223 A B f k).
Proof. exact (MK_COMB (@lem4618619 A) (@lem4618618 A B f k)). Qed.
Lemma lem4618621 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4618622 {A B : Type'} (x : A) (f : A -> B) (k : A -> B) : (term243 A B x f k) = (term257 A B x f k).
Proof. exact (MK_COMB (@lem4618621 A x) (@lem4618620 A B f k)). Qed.
Lemma lem4618623 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4618624 {A B : Type'} (x : A) (f : A -> B) (k : A -> B) : (term258 A B x f k) = (term259 A B x f k).
Proof. exact (MK_COMB (@lem4618623) (@lem4618622 A B x f k)). Qed.
Lemma lem4618625 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term244 A B f k x) = (term2 A B f k x).
Proof. exact (eq_refl (term244 A B f k x)). Qed.
Lemma lem4618626 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : ((term243 A B x f k) = (term244 A B f k x)) = ((term257 A B x f k) = (term2 A B f k x)).
Proof. exact (MK_COMB (@lem4618624 A B x f k) (@lem4618625 A B f k x)). Qed.
Lemma lem4618627 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term257 A B x f k) = (term2 A B f k x).
Proof. exact (EQ_MP (@lem4618626 A B f k x) (@lem4618609 A B f k x)). Qed.
Lemma lem4618630 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4618631 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term237 A B x f k) = (term260 A B f k x).
Proof. exact (MK_COMB (@lem4618630) (@lem4618627 A B f k x)). Qed.
Lemma lem4618633 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4618634 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4618633 A P x). Qed.
Lemma lem4618635 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4618634 A s x). Qed.
Lemma lem4618636 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (x : A) : (term297 A B f k x s) = (term298 A B f k s x).
Proof. exact (MK_COMB (@lem4618631 A B f k x) (@lem4618635 A s x)). Qed.
Lemma lem4618639 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) : (term299 A B f k s) = (term300 A B f k s).
Proof. exact (fun_ext (fun x : A => @lem4618636 A B f k s x)). Qed.
Lemma lem4618640 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4618641 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) : (term285 A B f k s) = (term301 A B f k s).
Proof. exact (MK_COMB (@lem4618640 A) (@lem4618639 A B f k s)). Qed.
Lemma lem4618646 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4618647 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) : (term287 A B f k s) = (term302 A B f k s).
Proof. exact (MK_COMB (@lem4618646) (@lem4618641 A B f k s)). Qed.
Lemma lem4618657 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term46 A B y f s) = (term47 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem4618658 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term46 A B y f s) = (term47 A B y f s).
Proof. exact (@lem4618657 A B y f s). Qed.
Lemma lem4618659 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term46 A B x f s) = (term47 A B x f s).
Proof. exact (@lem4618658 A B x f s). Qed.
Lemma lem4618669 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4618670 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4618669 A P x). Qed.
Lemma lem4618671 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4618670 A s x). Qed.
Lemma lem4618672 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term303 A B x f x') = (term303 A B x f x').
Proof. exact (eq_refl (term303 A B x f x')). Qed.
Lemma lem4618673 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term304 A B x f x' s) = (term305 A B x f s x').
Proof. exact (MK_COMB (@lem4618672 A B x f x') (@lem4618671 A s x')). Qed.
Lemma lem4618676 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term306 A B x f s) = (term307 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4618673 A B x f s x')). Qed.
Lemma lem4618677 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4618678 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term47 A B x f s) = (term308 A B x f s).
Proof. exact (MK_COMB (@lem4618677 A) (@lem4618676 A B x f s)). Qed.
Lemma lem4618683 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term46 A B x f s) = (term308 A B x f s).
Proof. exact (TRANS (@lem4618659 A B x f s) (@lem4618678 A B x f s)). Qed.
Lemma lem4618684 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4618685 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term309 A B x f s) = (term310 A B x f s).
Proof. exact (MK_COMB (@lem4618684) (@lem4618683 A B x f s)). Qed.
Lemma lem4618687 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4618688 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4618687 B P x). Qed.
Lemma lem4618689 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem4618688 B t x). Qed.
Lemma lem4618690 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term311 A B f s x t) = (term312 A B f s t x).
Proof. exact (MK_COMB (@lem4618685 A B x f s) (@lem4618689 B t x)). Qed.
Lemma lem4618693 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term313 A B f s t) = (term314 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem4618690 A B f s t x)). Qed.
Lemma lem4618694 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4618695 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term288 A B f s t) = (term315 A B f s t).
Proof. exact (MK_COMB (@lem4618694 B) (@lem4618693 A B f s t)). Qed.
Lemma lem4618700 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4618701 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term290 A B f s t) = (term316 A B f s t).
Proof. exact (MK_COMB (@lem4618700) (@lem4618695 A B f s t)). Qed.
Lemma lem4618704 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term282 A B t s) = (term282 A B t s).
Proof. exact (eq_refl (term282 A B t s)). Qed.
Lemma lem4618705 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term291 A B f t s) = (term317 A B f t s).
Proof. exact (MK_COMB (@lem4618701 A B f s t) (@lem4618704 A B t s)). Qed.
Lemma lem4618708 {A B : Type'} (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term292 A B k f t s) = (term318 A B k f t s).
Proof. exact (MK_COMB (@lem4618647 A B f k s) (@lem4618705 A B f t s)). Qed.
Lemma lem4618711 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4618712 {A B : Type'} (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term294 A B k f t s) = (term319 A B k f t s).
Proof. exact (MK_COMB (@lem4618711) (@lem4618708 A B k f t s)). Qed.
Lemma lem4618724 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4618725 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4618724 A P x). Qed.
Lemma lem4618726 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4618725 A s x). Qed.
Lemma lem4618727 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4618728 {A : Type'} (s : A -> Prop) (x : A) : (term320 A x s) = (term321 A s x).
Proof. exact (MK_COMB (@lem4618727) (@lem4618726 A s x)). Qed.
Lemma lem4618730 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4618731 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4618730 B P x). Qed.
Lemma lem4618732 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) : (term322 A B f x t) = (term323 A B t f x).
Proof. exact (@lem4618731 B t (f x)). Qed.
Lemma lem4618733 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term271 A B s f x t) = (term324 A B s t f x).
Proof. exact (MK_COMB (@lem4618728 A s x) (@lem4618732 A B t f x)). Qed.
Lemma lem4618736 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term260 A B f k x) = (term260 A B f k x).
Proof. exact (eq_refl (term260 A B f k x)). Qed.
Lemma lem4618737 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term272 A B k s f x t) = (term325 A B k s t f x).
Proof. exact (MK_COMB (@lem4618736 A B f k x) (@lem4618733 A B s t f x)). Qed.
Lemma lem4618740 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term273 A B k s f t) = (term326 A B k s t f).
Proof. exact (fun_ext (fun x : A => @lem4618737 A B k s t f x)). Qed.
Lemma lem4618741 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4618742 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term274 A B k s f t) = (term327 A B k s t f).
Proof. exact (MK_COMB (@lem4618741 A) (@lem4618740 A B k s t f)). Qed.
Lemma lem4618747 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term296 A B k s f t) = (term328 A B k s t f).
Proof. exact (MK_COMB (@lem4618712 A B k f t s) (@lem4618742 A B k s t f)). Qed.
Lemma lem4618750 {A B : Type'} (k : A -> B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term328 A B k s t f) = (term296 A B k s f t).
Proof. exact (SYM (@lem4618747 A B k s t f)). Qed.
Lemma lem4618752 (p : Prop) : p = (term329 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4618753 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term328 A B k s t f) = (term330 A B k s t f).
Proof. exact (@lem4618752 (term328 A B k s t f)). Qed.
Lemma lem4618754 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term330 A B k s t f) = (term328 A B k s t f).
Proof. exact (SYM (@lem4618753 A B k s t f)). Qed.
Lemma lem4618755 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term331 A B k s t f) : term331 A B k s t f.
Proof. exact (h1). Qed.
Lemma lem4618758 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term330 A B k s t f) : term330 A B k s t f.
Proof. exact (h1). Qed.
Lemma lem4618759 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) : term332 A B k s t f.
Proof. exact (fun h0 : term330 A B k s t f => @lem4618758 A B k s t f h0). Qed.
Lemma lem4618760 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term332 A B k s t f) : term332 A B k s t f.
Proof. exact (h1). Qed.
Lemma lem4618761 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term330 A B k s t f) : term330 A B k s t f.
Proof. exact (h1). Qed.
Lemma lem4618762 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term330 A B k s t f) (h2 : term332 A B k s t f) : term330 A B k s t f.
Proof. exact (@lem4618760 A B k s t f h2 (@lem4618761 A B k s t f h1)). Qed.
Lemma lem4618763 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term330 A B k s t f) : term333 A B k s t f.
Proof. exact (fun h0 : term332 A B k s t f => @lem4618762 A B k s t f h1 h0). Qed.
Lemma lem4618764 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term332 A B k s t f) : term332 A B k s t f.
Proof. exact (h1). Qed.
Lemma lem4618765 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term330 A B k s t f) (h2 : term332 A B k s t f) : term330 A B k s t f.
Proof. exact (@lem4618763 A B k s t f h1 (@lem4618764 A B k s t f h2)). Qed.
Lemma lem4618766 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term332 A B k s t f) : term332 A B k s t f.
Proof. exact (fun h0 : term330 A B k s t f => @lem4618765 A B k s t f h0 h1). Qed.
Lemma lem4618767 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) : term334 A B k s t f.
Proof. exact (fun h0 : term332 A B k s t f => @lem4618766 A B k s t f h0). Qed.
Lemma lem4618770 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) : term332 A B k s t f.
Proof. exact (@lem4618767 A B k s t f (@lem4618759 A B k s t f)). Qed.
Lemma lem4618771 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) : term332 A B k s t f.
Proof. exact (@lem4618770 A B k s t f). Qed.
Lemma lem4618789 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4618790 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term330 A B k s t f) = (term335 A B k s t f).
Proof. exact (@lem4618789 (term331 A B k s t f)). Qed.
Lemma lem4618792 (t : Prop) : (term336 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4618793 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term335 A B k s t f) = (term328 A B k s t f).
Proof. exact (@lem4618792 (term328 A B k s t f)). Qed.
Lemma lem4618796 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term330 A B k s t f) = (term328 A B k s t f).
Proof. exact (TRANS (@lem4618790 A B k s t f) (@lem4618793 A B k s t f)). Qed.
Lemma lem4618857 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term337 A B s t f) = (term338 A B s t f).
Proof. exact (fun_ext (fun k : A -> B => @lem4618796 A B k s t f)). Qed.
Lemma lem4618858 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4618859 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term339 A B s t f) = (term340 A B s t f).
Proof. exact (MK_COMB (@lem4618858 A B) (@lem4618857 A B s t f)). Qed.
Lemma lem4618864 {A B : Type'} (t : B -> Prop) (f : A -> B) : (term341 A B t f) = (term342 A B t f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4618859 A B s t f)). Qed.
Lemma lem4618865 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4618866 {A B : Type'} (t : B -> Prop) (f : A -> B) : (term343 A B t f) = (term344 A B t f).
Proof. exact (MK_COMB (@lem4618865 A) (@lem4618864 A B t f)). Qed.
Lemma lem4618871 {A B : Type'} (f : A -> B) : (term345 A B f) = (term346 A B f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4618866 A B t f)). Qed.
Lemma lem4618872 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4618873 {A B : Type'} (f : A -> B) : (term347 A B f) = (term348 A B f).
Proof. exact (MK_COMB (@lem4618872 B) (@lem4618871 A B f)). Qed.
Lemma lem4618878 {A B : Type'} : (term349 A B) = (term350 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4618873 A B f)). Qed.
Lemma lem4618879 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4618888 {A B : Type'} : (term351 A B) = (term352 A B).
Proof. exact (MK_COMB (@lem4618879 A B) (@lem4618878 A B)). Qed.
Lemma lem4618899 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term325 A B k s t f x) = (term325 A B k s t f x).
Proof. exact (eq_refl (term325 A B k s t f x)). Qed.
Lemma lem4618900 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term326 A B k s t f) = (term326 A B k s t f).
Proof. exact (fun_ext (fun x : A => @lem4618899 A B k s t f x)). Qed.
Lemma lem4618901 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4618902 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term327 A B k s t f) = (term327 A B k s t f).
Proof. exact (MK_COMB (@lem4618901 A) (@lem4618900 A B k s t f)). Qed.
Lemma lem4618907 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term282 A B t s) = (term282 A B t s).
Proof. exact (eq_refl (term282 A B t s)). Qed.
Lemma lem4618908 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem4618913 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term305 A B x f s x') = (term305 A B x f s x').
Proof. exact (eq_refl (term305 A B x f s x')). Qed.
Lemma lem4618914 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term307 A B x f s) = (term307 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4618913 A B x f s x')). Qed.
Lemma lem4618915 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4618916 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term308 A B x f s) = (term308 A B x f s).
Proof. exact (MK_COMB (@lem4618915 A) (@lem4618914 A B x f s)). Qed.
Lemma lem4618917 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4618918 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term310 A B x f s) = (term310 A B x f s).
Proof. exact (MK_COMB (@lem4618917) (@lem4618916 A B x f s)). Qed.
Lemma lem4618919 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term312 A B f s t x) = (term312 A B f s t x).
Proof. exact (MK_COMB (@lem4618918 A B x f s) (@lem4618908 B t x)). Qed.
Lemma lem4618920 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term314 A B f s t) = (term314 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem4618919 A B f s t x)). Qed.
Lemma lem4618921 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4618922 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term315 A B f s t) = (term315 A B f s t).
Proof. exact (MK_COMB (@lem4618921 B) (@lem4618920 A B f s t)). Qed.
Lemma lem4618923 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4618924 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term316 A B f s t) = (term316 A B f s t).
Proof. exact (MK_COMB (@lem4618923) (@lem4618922 A B f s t)). Qed.
Lemma lem4618925 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term317 A B f t s) = (term317 A B f t s).
Proof. exact (MK_COMB (@lem4618924 A B f s t) (@lem4618907 A B t s)). Qed.
Lemma lem4618932 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (x : A) : (term298 A B f k s x) = (term298 A B f k s x).
Proof. exact (eq_refl (term298 A B f k s x)). Qed.
Lemma lem4618933 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) : (term300 A B f k s) = (term300 A B f k s).
Proof. exact (fun_ext (fun x : A => @lem4618932 A B f k s x)). Qed.
Lemma lem4618934 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4618935 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) : (term301 A B f k s) = (term301 A B f k s).
Proof. exact (MK_COMB (@lem4618934 A) (@lem4618933 A B f k s)). Qed.
Lemma lem4618936 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4618937 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) : (term302 A B f k s) = (term302 A B f k s).
Proof. exact (MK_COMB (@lem4618936) (@lem4618935 A B f k s)). Qed.
Lemma lem4618938 {A B : Type'} (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term318 A B k f t s) = (term318 A B k f t s).
Proof. exact (MK_COMB (@lem4618937 A B f k s) (@lem4618925 A B f t s)). Qed.
Lemma lem4618939 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4618940 {A B : Type'} (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term319 A B k f t s) = (term319 A B k f t s).
Proof. exact (MK_COMB (@lem4618939) (@lem4618938 A B k f t s)). Qed.
Lemma lem4618941 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term328 A B k s t f) = (term328 A B k s t f).
Proof. exact (MK_COMB (@lem4618940 A B k f t s) (@lem4618902 A B k s t f)). Qed.
Lemma lem4618942 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term338 A B s t f) = (term338 A B s t f).
Proof. exact (fun_ext (fun k : A -> B => @lem4618941 A B k s t f)). Qed.
Lemma lem4618943 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4618944 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term340 A B s t f) = (term340 A B s t f).
Proof. exact (MK_COMB (@lem4618943 A B) (@lem4618942 A B s t f)). Qed.
Lemma lem4618945 {A B : Type'} (t : B -> Prop) (f : A -> B) : (term342 A B t f) = (term342 A B t f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4618944 A B s t f)). Qed.
Lemma lem4618946 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4618947 {A B : Type'} (t : B -> Prop) (f : A -> B) : (term344 A B t f) = (term344 A B t f).
Proof. exact (MK_COMB (@lem4618946 A) (@lem4618945 A B t f)). Qed.
Lemma lem4618948 {A B : Type'} (f : A -> B) : (term346 A B f) = (term346 A B f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4618947 A B t f)). Qed.
Lemma lem4618949 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4618950 {A B : Type'} (f : A -> B) : (term348 A B f) = (term348 A B f).
Proof. exact (MK_COMB (@lem4618949 B) (@lem4618948 A B f)). Qed.
Lemma lem4618951 {A B : Type'} : (term350 A B) = (term350 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4618950 A B f)). Qed.
Lemma lem4618952 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4618953 {A B : Type'} : (term352 A B) = (term352 A B).
Proof. exact (MK_COMB (@lem4618952 A B) (@lem4618951 A B)). Qed.
Lemma lem4619022 {A B : Type'} : (term351 A B) = (term352 A B).
Proof. exact (TRANS (@lem4618888 A B) (@lem4618953 A B)). Qed.
Lemma lem4619023 {A B : Type'} : (term352 A B) = (term351 A B).
Proof. exact (SYM (@lem4619022 A B)). Qed.
Lemma lem4619024 {A B : Type'} (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term318 A B k f t s.
Proof. exact (h1). Qed.
Lemma lem4619027 (p : Prop) : p = (term329 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4619028 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term324 A B s t f x) = (term353 A B s t f x).
Proof. exact (@lem4619027 (term324 A B s t f x)). Qed.
Lemma lem4619029 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term353 A B s t f x) = (term324 A B s t f x).
Proof. exact (SYM (@lem4619028 A B s t f x)). Qed.
Lemma lem4619030 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term354 A B s t f x) : term354 A B s t f x.
Proof. exact (h1). Qed.
Lemma lem4619033 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term355 A B f k x) = ((f x) = (k x)).
Proof. exact (@lem16933 ((f x) = (k x))). Qed.
Lemma lem4619034 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem4619035 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4619036 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term356 A B f k x) = (term357 A B f k x).
Proof. exact (MK_COMB (@lem4619035) (@lem4619033 A B f k x)). Qed.
Lemma lem4619037 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (x : A) : (term358 A B f k s x) = (term359 A B f k s x).
Proof. exact (MK_COMB (@lem4619036 A B f k x) (@lem4619034 A s x)). Qed.
Lemma lem4619038 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (x : A) : (term298 A B f k s x) = (term358 A B f k s x).
Proof. exact (@lem17265 (term2 A B f k x) (s x)). Qed.
Lemma lem4619039 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (x : A) : (term298 A B f k s x) = (term359 A B f k s x).
Proof. exact (TRANS (@lem4619038 A B f k s x) (@lem4619037 A B f k s x)). Qed.
Lemma lem4619040 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) : (term300 A B f k s) = (term360 A B f k s).
Proof. exact (fun_ext (fun x : A => @lem4619039 A B f k s x)). Qed.
Lemma lem4619041 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4619042 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) : (term301 A B f k s) = (term361 A B f k s).
Proof. exact (MK_COMB (@lem4619041 A) (@lem4619040 A B f k s)). Qed.
Lemma lem4619049 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term362 A B x f s x') = (term363 A B x f s x').
Proof. exact (@lem17045 (x = (f x')) (s x')). Qed.
Lemma lem4619050 {A : Type'} (P : A -> Prop) : (term364 A P) = (term365 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4619051 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term366 A B x f s) = (term367 A B x f s).
Proof. exact (@lem4619050 A (term307 A B x f s)). Qed.
Lemma lem4619052 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term368 A B x f s x') = (term305 A B x f s x').
Proof. exact (eq_refl (term368 A B x f s x')). Qed.
Lemma lem4619053 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4619054 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term369 A B x f s x') = (term362 A B x f s x').
Proof. exact (MK_COMB (@lem4619053) (@lem4619052 A B x f s x')). Qed.
Lemma lem4619055 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term369 A B x f s x') = (term363 A B x f s x').
Proof. exact (TRANS (@lem4619054 A B x f s x') (@lem4619049 A B x f s x')). Qed.
Lemma lem4619056 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term370 A B x f s) = (term371 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4619055 A B x f s x')). Qed.
Lemma lem4619057 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4619058 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term367 A B x f s) = (term372 A B x f s).
Proof. exact (MK_COMB (@lem4619057 A) (@lem4619056 A B x f s)). Qed.
Lemma lem4619059 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term366 A B x f s) = (term372 A B x f s).
Proof. exact (TRANS (@lem4619051 A B x f s) (@lem4619058 A B x f s)). Qed.
Lemma lem4619060 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem4619061 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4619062 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term373 A B x f s) = (term374 A B x f s).
Proof. exact (MK_COMB (@lem4619061) (@lem4619059 A B x f s)). Qed.
Lemma lem4619063 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term375 A B f s t x) = (term376 A B f s t x).
Proof. exact (MK_COMB (@lem4619062 A B x f s) (@lem4619060 B t x)). Qed.
Lemma lem4619064 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term312 A B f s t x) = (term375 A B f s t x).
Proof. exact (@lem17265 (term308 A B x f s) (t x)). Qed.
Lemma lem4619065 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term312 A B f s t x) = (term376 A B f s t x).
Proof. exact (TRANS (@lem4619064 A B f s t x) (@lem4619063 A B f s t x)). Qed.
Lemma lem4619066 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term314 A B f s t) = (term377 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem4619065 A B f s t x)). Qed.
Lemma lem4619067 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4619068 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term315 A B f s t) = (term378 A B f s t).
Proof. exact (MK_COMB (@lem4619067 B) (@lem4619066 A B f s t)). Qed.
Lemma lem4619073 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term282 A B t s) = (term282 A B t s).
Proof. exact (eq_refl (term282 A B t s)). Qed.
Lemma lem4619074 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4619075 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term316 A B f s t) = (term379 A B f s t).
Proof. exact (MK_COMB (@lem4619074) (@lem4619068 A B f s t)). Qed.
Lemma lem4619076 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term317 A B f t s) = (term380 A B f t s).
Proof. exact (MK_COMB (@lem4619075 A B f s t) (@lem4619073 A B t s)). Qed.
Lemma lem4619077 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4619078 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) : (term302 A B f k s) = (term381 A B f k s).
Proof. exact (MK_COMB (@lem4619077) (@lem4619042 A B f k s)). Qed.
Lemma lem4619195 {A B : Type'} (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term318 A B k f t s) = (term382 A B k f t s).
Proof. exact (MK_COMB (@lem4619078 A B f k s) (@lem4619076 A B f t s)). Qed.
Lemma lem4619196 {A B : Type'} (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term382 A B k f t s.
Proof. exact (EQ_MP (@lem4619195 A B k f t s) (@lem4619024 A B k f t s h1)). Qed.
Lemma lem4619202 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : term2 A B f k x.
Proof. exact (h1). Qed.
Lemma lem4619213 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term354 A B s t f x) = (term383 A B s t f x).
Proof. exact (@lem17045 (s x) (term323 A B t f x)). Qed.
Lemma lem4619214 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term354 A B s t f x) : term383 A B s t f x.
Proof. exact (EQ_MP (@lem4619213 A B s t f x) (@lem4619030 A B s t f x h1)). Qed.
Lemma lem4619223 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term282 A B t s) = (term282 A B t s).
Proof. exact (eq_refl (term282 A B t s)). Qed.
Lemma lem4619228 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4619229 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem4619228 B Prop f x). Qed.
Lemma lem4619231 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (@I (B -> Prop) t x).
Proof. exact (@lem4619229 B t x). Qed.
Lemma lem4619232 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4619237 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4619238 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4619237 A Prop f x). Qed.
Lemma lem4619240 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4619238 A s x). Qed.
Lemma lem4619241 {A : Type'} (s : A -> Prop) (x : A) : (term384 A s x) = (term385 A s x).
Proof. exact (MK_COMB (@lem4619232) (@lem4619240 A s x)). Qed.
Lemma lem4619252 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term386 A B x f x') = (term386 A B x f x').
Proof. exact (eq_refl (term386 A B x f x')). Qed.
Lemma lem4619253 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term363 A B x f s x') = (term387 A B x f s x').
Proof. exact (MK_COMB (@lem4619252 A B x f x') (@lem4619241 A s x')). Qed.
Lemma lem4619254 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term371 A B x f s) = (term388 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4619253 A B x f s x')). Qed.
Lemma lem4619255 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4619256 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term372 A B x f s) = (term389 A B x f s).
Proof. exact (MK_COMB (@lem4619255 A) (@lem4619254 A B x f s)). Qed.
Lemma lem4619257 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4619258 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term374 A B x f s) = (term390 A B x f s).
Proof. exact (MK_COMB (@lem4619257) (@lem4619256 A B x f s)). Qed.
Lemma lem4619259 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term376 A B f s t x) = (term391 A B f s t x).
Proof. exact (MK_COMB (@lem4619258 A B x f s) (@lem4619231 B t x)). Qed.
Lemma lem4619260 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term377 A B f s t) = (term392 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem4619259 A B f s t x)). Qed.
Lemma lem4619261 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4619262 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term378 A B f s t) = (term393 A B f s t).
Proof. exact (MK_COMB (@lem4619261 B) (@lem4619260 A B f s t)). Qed.
Lemma lem4619263 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4619264 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term379 A B f s t) = (term394 A B f s t).
Proof. exact (MK_COMB (@lem4619263) (@lem4619262 A B f s t)). Qed.
Lemma lem4619265 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term380 A B f t s) = (term395 A B f t s).
Proof. exact (MK_COMB (@lem4619264 A B f s t) (@lem4619223 A B t s)). Qed.
Lemma lem4619270 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4619271 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4619270 A Prop f x). Qed.
Lemma lem4619273 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4619271 A s x). Qed.
Lemma lem4619284 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term357 A B f k x) = (term357 A B f k x).
Proof. exact (eq_refl (term357 A B f k x)). Qed.
Lemma lem4619285 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (x : A) : (term359 A B f k s x) = (term396 A B f k s x).
Proof. exact (MK_COMB (@lem4619284 A B f k x) (@lem4619273 A s x)). Qed.
Lemma lem4619286 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) : (term360 A B f k s) = (term397 A B f k s).
Proof. exact (fun_ext (fun x : A => @lem4619285 A B f k s x)). Qed.
Lemma lem4619287 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4619288 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) : (term361 A B f k s) = (term398 A B f k s).
Proof. exact (MK_COMB (@lem4619287 A) (@lem4619286 A B f k s)). Qed.
Lemma lem4619289 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4619290 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) : (term381 A B f k s) = (term399 A B f k s).
Proof. exact (MK_COMB (@lem4619289) (@lem4619288 A B f k s)). Qed.
Lemma lem4619291 {A B : Type'} (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term382 A B k f t s) = (term400 A B k f t s).
Proof. exact (MK_COMB (@lem4619290 A B f k s) (@lem4619265 A B f t s)). Qed.
Lemma lem4619292 {A B : Type'} (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term400 A B k f t s.
Proof. exact (EQ_MP (@lem4619291 A B k f t s) (@lem4619196 A B k f t s h1)). Qed.
Lemma lem4619304 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : term2 A B f k x.
Proof. exact (h1). Qed.
Lemma lem4619305 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4619312 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4619313 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem4619312 B Prop f x). Qed.
Lemma lem4619315 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) : (term323 A B t f x) = (term401 A B t f x).
Proof. exact (@lem4619313 B t (f x)). Qed.
Lemma lem4619316 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) : (term402 A B t f x) = (term403 A B t f x).
Proof. exact (MK_COMB (@lem4619305) (@lem4619315 A B t f x)). Qed.
Lemma lem4619317 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4619322 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4619323 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4619322 A Prop f x). Qed.
Lemma lem4619325 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4619323 A s x). Qed.
Lemma lem4619326 {A : Type'} (s : A -> Prop) (x : A) : (term384 A s x) = (term385 A s x).
Proof. exact (MK_COMB (@lem4619317) (@lem4619325 A s x)). Qed.
Lemma lem4619327 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4619328 {A : Type'} (s : A -> Prop) (x : A) : (term404 A s x) = (term405 A s x).
Proof. exact (MK_COMB (@lem4619327) (@lem4619326 A s x)). Qed.
Lemma lem4619329 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term383 A B s t f x) = (term406 A B s t f x).
Proof. exact (MK_COMB (@lem4619328 A s x) (@lem4619316 A B t f x)). Qed.
Lemma lem4619330 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) (h1 : term354 A B s t f x) : term406 A B s t f x.
Proof. exact (EQ_MP (@lem4619329 A B s t f x) (@lem4619214 A B s t f x h1)). Qed.
Lemma lem4619331 {A B : Type'} (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term395 A B f t s.
Proof. exact (proj2 (@lem4619292 A B k f t s h1)). Qed.
Lemma lem4619332 {A B : Type'} (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term398 A B f k s.
Proof. exact (proj1 (@lem4619292 A B k f t s h1)). Qed.
Lemma lem4619334 {A B : Type'} (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term393 A B f s t.
Proof. exact (proj1 (@lem4619331 A B k f t s h1)). Qed.
Lemma lem4619342 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : term2 A B f k x.
Proof. exact (h1). Qed.
Lemma lem4619350 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (x : A) : (term396 A B f k s x) = (term396 A B f k s x).
Proof. exact (eq_refl (term396 A B f k s x)). Qed.
Lemma lem4619351 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) : (term397 A B f k s) = (term397 A B f k s).
Proof. exact (fun_ext (fun x : A => @lem4619350 A B f k s x)). Qed.
Lemma lem4619352 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4619354 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) : (term398 A B f k s) = (term398 A B f k s).
Proof. exact (MK_COMB (@lem4619352 A) (@lem4619351 A B f k s)). Qed.
Lemma lem4619355 {A B : Type'} (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term398 A B f k s.
Proof. exact (EQ_MP (@lem4619354 A B f k s) (@lem4619332 A B k f t s h1)). Qed.
Lemma lem4619415 {A : Type'} (s : A -> Prop) (x : A) (h1 : term385 A s x) : term385 A s x.
Proof. exact (h1). Qed.
Lemma lem4619419 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : term2 A B f k x.
Proof. exact (h1). Qed.
Lemma lem4619427 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (x : A) : (term396 A B f k s x) = (term396 A B f k s x).
Proof. exact (eq_refl (term396 A B f k s x)). Qed.
Lemma lem4619428 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) : (term397 A B f k s) = (term397 A B f k s).
Proof. exact (fun_ext (fun x : A => @lem4619427 A B f k s x)). Qed.
Lemma lem4619429 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4619431 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) : (term398 A B f k s) = (term398 A B f k s).
Proof. exact (MK_COMB (@lem4619429 A) (@lem4619428 A B f k s)). Qed.
Lemma lem4619432 {A B : Type'} (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term398 A B f k s.
Proof. exact (EQ_MP (@lem4619431 A B f k s) (@lem4619332 A B k f t s h1)). Qed.
Lemma lem4619434 {A : Type'} (P : A -> Prop) (Q : Prop) : (term407 A P Q) = (term408 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem4619435 {A : Type'} (P : A -> Prop) (Q : Prop) : (term407 A P Q) = (term408 A P Q).
Proof. exact (@lem4619434 A P Q). Qed.
Lemma lem4619436 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term409 A B f s t x) = (term410 A B f s t x).
Proof. exact (@lem4619435 A (term388 A B x f s) (@I (B -> Prop) t x)). Qed.
Lemma lem4619437 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term411 A B x f s x') = (term387 A B x f s x').
Proof. exact (eq_refl (term411 A B x f s x')). Qed.
Lemma lem4619438 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term412 A B x f s) = (term388 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4619437 A B x f s x')). Qed.
Lemma lem4619439 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4619440 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term413 A B x f s) = (term389 A B x f s).
Proof. exact (MK_COMB (@lem4619439 A) (@lem4619438 A B x f s)). Qed.
Lemma lem4619441 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4619442 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term414 A B x f s) = (term390 A B x f s).
Proof. exact (MK_COMB (@lem4619441) (@lem4619440 A B x f s)). Qed.
Lemma lem4619443 {B : Type'} (t : B -> Prop) (x : B) : (@I (B -> Prop) t x) = (@I (B -> Prop) t x).
Proof. exact (eq_refl (@I (B -> Prop) t x)). Qed.
Lemma lem4619444 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term409 A B f s t x) = (term391 A B f s t x).
Proof. exact (MK_COMB (@lem4619442 A B x f s) (@lem4619443 B t x)). Qed.
Lemma lem4619445 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4619446 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term415 A B f s t x) = (term416 A B f s t x).
Proof. exact (MK_COMB (@lem4619445) (@lem4619444 A B f s t x)). Qed.
Lemma lem4619447 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term411 A B x f s x') = (term387 A B x f s x').
Proof. exact (eq_refl (term411 A B x f s x')). Qed.
Lemma lem4619448 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4619449 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term417 A B x f s x') = (term418 A B x f s x').
Proof. exact (MK_COMB (@lem4619448) (@lem4619447 A B x f s x')). Qed.
Lemma lem4619450 {B : Type'} (t : B -> Prop) (x : B) : (@I (B -> Prop) t x) = (@I (B -> Prop) t x).
Proof. exact (eq_refl (@I (B -> Prop) t x)). Qed.
Lemma lem4619451 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term419 A B f s x t x') = (term420 A B f s x t x').
Proof. exact (MK_COMB (@lem4619449 A B x' f s x) (@lem4619450 B t x')). Qed.
Lemma lem4619452 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term421 A B f s t x) = (term422 A B f s t x).
Proof. exact (fun_ext (fun x' : A => @lem4619451 A B f s x' t x)). Qed.
Lemma lem4619453 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4619454 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term410 A B f s t x) = (term423 A B f s t x).
Proof. exact (MK_COMB (@lem4619453 A) (@lem4619452 A B f s t x)). Qed.
Lemma lem4619455 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : ((term409 A B f s t x) = (term410 A B f s t x)) = ((term391 A B f s t x) = (term423 A B f s t x)).
Proof. exact (MK_COMB (@lem4619446 A B f s t x) (@lem4619454 A B f s t x)). Qed.
Lemma lem4619456 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term391 A B f s t x) = (term423 A B f s t x).
Proof. exact (EQ_MP (@lem4619455 A B f s t x) (@lem4619436 A B f s t x)). Qed.
Lemma lem4619457 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term392 A B f s t) = (term424 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem4619456 A B f s t x)). Qed.
Lemma lem4619458 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4619459 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term393 A B f s t) = (term425 A B f s t).
Proof. exact (MK_COMB (@lem4619458 B) (@lem4619457 A B f s t)). Qed.
Lemma lem4619472 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term420 A B f s x t x') = (term420 A B f s x t x').
Proof. exact (eq_refl (term420 A B f s x t x')). Qed.
Lemma lem4619473 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term422 A B f s t x) = (term422 A B f s t x).
Proof. exact (fun_ext (fun x' : A => @lem4619472 A B f s x' t x)). Qed.
Lemma lem4619474 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4619475 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term423 A B f s t x) = (term423 A B f s t x).
Proof. exact (MK_COMB (@lem4619474 A) (@lem4619473 A B f s t x)). Qed.
Lemma lem4619476 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term424 A B f s t) = (term424 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem4619475 A B f s t x)). Qed.
Lemma lem4619477 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4619478 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term425 A B f s t) = (term425 A B f s t).
Proof. exact (MK_COMB (@lem4619477 B) (@lem4619476 A B f s t)). Qed.
Lemma lem4619479 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term393 A B f s t) = (term425 A B f s t).
Proof. exact (TRANS (@lem4619459 A B f s t) (@lem4619478 A B f s t)). Qed.
Lemma lem4619480 {A B : Type'} (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term425 A B f s t.
Proof. exact (EQ_MP (@lem4619479 A B f s t) (@lem4619334 A B k f t s h1)). Qed.
Lemma lem4619492 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) (h1 : term403 A B t f x) : term403 A B t f x.
Proof. exact (h1). Qed.
Lemma lem4619493 {A B : Type'} (_55480 : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term426 A B f k s _55480.
Proof. exact (@lem4619355 A B k f t s h1 _55480). Qed.
Lemma lem4619494 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (_55480 : A) : (term426 A B f k s _55480) = (term396 A B f k s _55480).
Proof. exact (eq_refl (term426 A B f k s _55480)). Qed.
Lemma lem4619502 {A B : Type'} (_55483 : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term426 A B f k s _55483.
Proof. exact (@lem4619432 A B k f t s h1 _55483). Qed.
Lemma lem4619503 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (_55483 : A) : (term426 A B f k s _55483) = (term396 A B f k s _55483).
Proof. exact (eq_refl (term426 A B f k s _55483)). Qed.
Lemma lem4619505 {A B : Type'} (_55484 : B) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term427 A B f s t _55484.
Proof. exact (@lem4619480 A B k f t s h1 _55484). Qed.
Lemma lem4619506 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (_55484 : B) : (term427 A B f s t _55484) = (term423 A B f s t _55484).
Proof. exact (eq_refl (term427 A B f s t _55484)). Qed.
Lemma lem4619507 {A B : Type'} (_55484 : B) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term423 A B f s t _55484.
Proof. exact (EQ_MP (@lem4619506 A B f s t _55484) (@lem4619505 A B _55484 k f t s h1)). Qed.
Lemma lem4619508 {A B : Type'} (_55484 : B) (_55485 : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term428 A B f s t _55484 _55485.
Proof. exact (@lem4619507 A B _55484 k f t s h1 _55485). Qed.
Lemma lem4619509 {A B : Type'} (f : A -> B) (s : A -> Prop) (_55485 : A) (t : B -> Prop) (_55484 : B) : (term428 A B f s t _55484 _55485) = (term420 A B f s _55485 t _55484).
Proof. exact (eq_refl (term428 A B f s t _55484 _55485)). Qed.
Lemma lem4619510 {A B : Type'} (_55485 : A) (_55484 : B) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term420 A B f s _55485 t _55484.
Proof. exact (EQ_MP (@lem4619509 A B f s _55485 t _55484) (@lem4619508 A B _55484 _55485 k f t s h1)). Qed.
Lemma lem4619512 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : term2 A B f k x.
Proof. exact (h1). Qed.
Lemma lem4619518 {A B : Type'} (_55480 : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term396 A B f k s _55480.
Proof. exact (EQ_MP (@lem4619494 A B f k s _55480) (@lem4619493 A B _55480 k f t s h1)). Qed.
Lemma lem4619536 {A : Type'} (s : A -> Prop) (x : A) (h1 : term385 A s x) : term385 A s x.
Proof. exact (h1). Qed.
Lemma lem4619538 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : term2 A B f k x.
Proof. exact (h1). Qed.
Lemma lem4619544 {A B : Type'} (_55483 : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term396 A B f k s _55483.
Proof. exact (EQ_MP (@lem4619503 A B f k s _55483) (@lem4619502 A B _55483 k f t s h1)). Qed.
Lemma lem4619555 {A B : Type'} (f : A -> B) (s : A -> Prop) (_55485 : A) (t : B -> Prop) (_55484 : B) : (term420 A B f s _55485 t _55484) = (term429 A B f s _55485 t _55484).
Proof. exact (@lem4618526 (term430 A B _55484 f _55485) (term385 A s _55485) (@I (B -> Prop) t _55484)). Qed.
Lemma lem4619556 {A B : Type'} (_55485 : A) (_55484 : B) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term429 A B f s _55485 t _55484.
Proof. exact (EQ_MP (@lem4619555 A B f s _55485 t _55484) (@lem4619510 A B _55485 _55484 k f t s h1)). Qed.
Lemma lem4619562 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) (h1 : term403 A B t f x) : term403 A B t f x.
Proof. exact (h1). Qed.
Lemma lem4619650 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : term2 A B f k x.
Proof. exact (h1). Qed.
Lemma lem4619651 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : term431 A B f k x.
Proof. exact (fun h0 : (f x) = (k x) => @lem4619650 A B f k x h1). Qed.
Lemma lem4619653 (p : Prop) : (term432 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4619654 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term431 A B f k x) = (term2 A B f k x).
Proof. exact (@lem4619653 ((f x) = (k x))). Qed.
Lemma lem4619655 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : term2 A B f k x.
Proof. exact (EQ_MP (@lem4619654 A B f k x) (@lem4619651 A B f k x h1)). Qed.
Lemma lem4619668 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4619669 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (_55480 : A) : (term433 A B s f k _55480) = (term396 A B f k s _55480).
Proof. exact (@lem4619668 ((f _55480) = (k _55480)) (@I (A -> Prop) s _55480)). Qed.
Lemma lem4619677 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (_55480 : A) : (term434 A B f k s _55480) = (term434 A B f k s _55480).
Proof. exact (eq_refl (term434 A B f k s _55480)). Qed.
Lemma lem4619678 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (_55480 : A) : ((term396 A B f k s _55480) = (term433 A B s f k _55480)) = ((term396 A B f k s _55480) = (term396 A B f k s _55480)).
Proof. exact (MK_COMB (@lem4619677 A B f k s _55480) (@lem4619669 A B f k s _55480)). Qed.
Lemma lem4619680 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4619681 (x : Prop) : (x = x) = True.
Proof. exact (@lem4619680 Prop x). Qed.
Lemma lem4619682 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (_55480 : A) : ((term396 A B f k s _55480) = (term396 A B f k s _55480)) = True.
Proof. exact (@lem4619681 (term396 A B f k s _55480)). Qed.
Lemma lem4619683 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> B) (_55480 : A) : ((term396 A B f k s _55480) = (term433 A B s f k _55480)) = True.
Proof. exact (TRANS (@lem4619678 A B f k s _55480) (@lem4619682 A B f k s _55480)). Qed.
Lemma lem4619684 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> B) (_55480 : A) : True = ((term396 A B f k s _55480) = (term433 A B s f k _55480)).
Proof. exact (SYM (@lem4619683 A B s f k _55480)). Qed.
Lemma lem4619685 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> B) (_55480 : A) : (term396 A B f k s _55480) = (term433 A B s f k _55480).
Proof. exact (EQ_MP (@lem4619684 A B s f k _55480) (@lem0)). Qed.
Lemma lem4619686 {A B : Type'} (_55480 : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term433 A B s f k _55480.
Proof. exact (EQ_MP (@lem4619685 A B s f k _55480) (@lem4619518 A B _55480 k f t s h1)). Qed.
Lemma lem4619688 (b : Prop) (a : Prop) : (a \/ b) = (term435 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4619691 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (_55480 : A) : (term433 A B s f k _55480) = (term436 A B f k s _55480).
Proof. exact (@lem4619688 ((f _55480) = (k _55480)) (@I (A -> Prop) s _55480)). Qed.
Lemma lem4619694 {A B : Type'} (_55480 : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term436 A B f k s _55480.
Proof. exact (EQ_MP (@lem4619691 A B f k s _55480) (@lem4619686 A B _55480 k f t s h1)). Qed.
Lemma lem4619695 {A B : Type'} (_55480 : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term436 A B f k s _55480.
Proof. exact (@lem4619694 A B _55480 k f t s h1). Qed.
Lemma lem4619696 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term436 A B f k s x.
Proof. exact (@lem4619695 A B x k f t s h1). Qed.
Lemma lem4619699 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term318 A B k f t s) : @I (A -> Prop) s x.
Proof. exact (@lem4619696 A B x k f t s h2 (@lem4619655 A B f k x h1)). Qed.
Lemma lem4619700 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term318 A B k f t s) : term437 A s x.
Proof. exact (fun h0 : term385 A s x => @lem4619699 A B x k f t s h1 h2). Qed.
Lemma lem4619702 (p : Prop) : (term438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4619703 {A : Type'} (s : A -> Prop) (x : A) : (term437 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4619702 (@I (A -> Prop) s x)). Qed.
Lemma lem4619704 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term318 A B k f t s) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem4619703 A s x) (@lem4619700 A B x k f t s h1 h2)). Qed.
Lemma lem4619707 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4619709 {A : Type'} (s : A -> Prop) (x : A) : (term385 A s x) = (term439 A s x).
Proof. exact (@lem4619707 (@I (A -> Prop) s x)). Qed.
Lemma lem4619712 {A : Type'} (s : A -> Prop) (x : A) (h1 : term385 A s x) : term439 A s x.
Proof. exact (EQ_MP (@lem4619709 A s x) (@lem4619536 A s x h1)). Qed.
Lemma lem4619715 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term385 A s x) (h3 : term318 A B k f t s) : False.
Proof. exact (@lem4619712 A s x h2 (@lem4619704 A B x k f t s h1 h3)). Qed.
Lemma lem4619716 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term385 A s x) (h3 : term318 A B k f t s) : term440.
Proof. exact (fun h0 : ~ False => @lem4619715 A B x k f t s h1 h2 h3). Qed.
Lemma lem4619718 (p : Prop) : (term438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4619719 : term440 = False.
Proof. exact (@lem4619718 False). Qed.
Lemma lem4619720 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term385 A s x) (h3 : term318 A B k f t s) : False.
Proof. exact (EQ_MP (@lem4619719) (@lem4619716 A B x k f t s h1 h2 h3)). Qed.
Lemma lem4619808 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem4619809 {B : Type'} (x : B) : x = x.
Proof. exact (@lem4619808 B x). Qed.
Lemma lem4619810 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (@lem4619809 B (f x)). Qed.
Lemma lem4619811 {A B : Type'} (f : A -> B) (x : A) : term441 A B f x.
Proof. exact (fun h0 : term442 A B f x => @lem4619810 A B f x). Qed.
Lemma lem4619813 (p : Prop) : (term438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4619814 {A B : Type'} (f : A -> B) (x : A) : (term441 A B f x) = ((f x) = (f x)).
Proof. exact (@lem4619813 ((f x) = (f x))). Qed.
Lemma lem4619815 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (EQ_MP (@lem4619814 A B f x) (@lem4619811 A B f x)). Qed.
Lemma lem4619817 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : term2 A B f k x.
Proof. exact (h1). Qed.
Lemma lem4619818 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : term431 A B f k x.
Proof. exact (fun h0 : (f x) = (k x) => @lem4619817 A B f k x h1). Qed.
Lemma lem4619820 (p : Prop) : (term432 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4619821 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term431 A B f k x) = (term2 A B f k x).
Proof. exact (@lem4619820 ((f x) = (k x))). Qed.
Lemma lem4619822 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : term2 A B f k x.
Proof. exact (EQ_MP (@lem4619821 A B f k x) (@lem4619818 A B f k x h1)). Qed.
Lemma lem4619835 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4619836 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (_55483 : A) : (term433 A B s f k _55483) = (term396 A B f k s _55483).
Proof. exact (@lem4619835 ((f _55483) = (k _55483)) (@I (A -> Prop) s _55483)). Qed.
Lemma lem4619844 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (_55483 : A) : (term434 A B f k s _55483) = (term434 A B f k s _55483).
Proof. exact (eq_refl (term434 A B f k s _55483)). Qed.
Lemma lem4619845 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (_55483 : A) : ((term396 A B f k s _55483) = (term433 A B s f k _55483)) = ((term396 A B f k s _55483) = (term396 A B f k s _55483)).
Proof. exact (MK_COMB (@lem4619844 A B f k s _55483) (@lem4619836 A B f k s _55483)). Qed.
Lemma lem4619847 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4619848 (x : Prop) : (x = x) = True.
Proof. exact (@lem4619847 Prop x). Qed.
Lemma lem4619849 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (_55483 : A) : ((term396 A B f k s _55483) = (term396 A B f k s _55483)) = True.
Proof. exact (@lem4619848 (term396 A B f k s _55483)). Qed.
Lemma lem4619850 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> B) (_55483 : A) : ((term396 A B f k s _55483) = (term433 A B s f k _55483)) = True.
Proof. exact (TRANS (@lem4619845 A B f k s _55483) (@lem4619849 A B f k s _55483)). Qed.
Lemma lem4619851 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> B) (_55483 : A) : True = ((term396 A B f k s _55483) = (term433 A B s f k _55483)).
Proof. exact (SYM (@lem4619850 A B s f k _55483)). Qed.
Lemma lem4619852 {A B : Type'} (s : A -> Prop) (f : A -> B) (k : A -> B) (_55483 : A) : (term396 A B f k s _55483) = (term433 A B s f k _55483).
Proof. exact (EQ_MP (@lem4619851 A B s f k _55483) (@lem0)). Qed.
Lemma lem4619853 {A B : Type'} (_55483 : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term433 A B s f k _55483.
Proof. exact (EQ_MP (@lem4619852 A B s f k _55483) (@lem4619544 A B _55483 k f t s h1)). Qed.
Lemma lem4619855 (b : Prop) (a : Prop) : (a \/ b) = (term435 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4619858 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (_55483 : A) : (term433 A B s f k _55483) = (term436 A B f k s _55483).
Proof. exact (@lem4619855 ((f _55483) = (k _55483)) (@I (A -> Prop) s _55483)). Qed.
Lemma lem4619861 {A B : Type'} (_55483 : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term436 A B f k s _55483.
Proof. exact (EQ_MP (@lem4619858 A B f k s _55483) (@lem4619853 A B _55483 k f t s h1)). Qed.
Lemma lem4619862 {A B : Type'} (_55483 : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term436 A B f k s _55483.
Proof. exact (@lem4619861 A B _55483 k f t s h1). Qed.
Lemma lem4619863 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term436 A B f k s x.
Proof. exact (@lem4619862 A B x k f t s h1). Qed.
Lemma lem4619866 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term318 A B k f t s) : @I (A -> Prop) s x.
Proof. exact (@lem4619863 A B x k f t s h2 (@lem4619822 A B f k x h1)). Qed.
Lemma lem4619867 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term318 A B k f t s) : term437 A s x.
Proof. exact (fun h0 : term385 A s x => @lem4619866 A B x k f t s h1 h2). Qed.
Lemma lem4619869 (p : Prop) : (term438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4619870 {A : Type'} (s : A -> Prop) (x : A) : (term437 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4619869 (@I (A -> Prop) s x)). Qed.
Lemma lem4619871 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term318 A B k f t s) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem4619870 A s x) (@lem4619867 A B x k f t s h1 h2)). Qed.
Lemma lem4619889 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4619890 {A B : Type'} (t : B -> Prop) (_55484 : B) (s : A -> Prop) (_55485 : A) : (term443 A B s _55485 t _55484) = (term444 A B t _55484 s _55485).
Proof. exact (@lem4619889 (@I (B -> Prop) t _55484) (term385 A s _55485)). Qed.
Lemma lem4619896 {A B : Type'} (_55484 : B) (f : A -> B) (_55485 : A) : (term386 A B _55484 f _55485) = (term386 A B _55484 f _55485).
Proof. exact (eq_refl (term386 A B _55484 f _55485)). Qed.
Lemma lem4619897 {A B : Type'} (f : A -> B) (t : B -> Prop) (_55484 : B) (s : A -> Prop) (_55485 : A) : (term429 A B f s _55485 t _55484) = (term445 A B f t _55484 s _55485).
Proof. exact (MK_COMB (@lem4619896 A B _55484 f _55485) (@lem4619890 A B t _55484 s _55485)). Qed.
Lemma lem4619901 (q : Prop) (p : Prop) (r : Prop) : (term280 p q r) = (term280 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4619902 {A B : Type'} (t : B -> Prop) (_55484 : B) (f : A -> B) (s : A -> Prop) (_55485 : A) : (term445 A B f t _55484 s _55485) = (term446 A B t _55484 f s _55485).
Proof. exact (@lem4619901 (@I (B -> Prop) t _55484) (term430 A B _55484 f _55485) (term385 A s _55485)). Qed.
Lemma lem4619920 {A B : Type'} (t : B -> Prop) (_55484 : B) (f : A -> B) (s : A -> Prop) (_55485 : A) : (term429 A B f s _55485 t _55484) = (term446 A B t _55484 f s _55485).
Proof. exact (TRANS (@lem4619897 A B f t _55484 s _55485) (@lem4619902 A B t _55484 f s _55485)). Qed.
Lemma lem4619921 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4619922 {A B : Type'} (t : B -> Prop) (_55484 : B) (f : A -> B) (s : A -> Prop) (_55485 : A) : (term447 A B f s _55485 t _55484) = (term448 A B t _55484 f s _55485).
Proof. exact (MK_COMB (@lem4619921) (@lem4619920 A B t _55484 f s _55485)). Qed.
Lemma lem4619940 {A B : Type'} (t : B -> Prop) (_55484 : B) (f : A -> B) (s : A -> Prop) (_55485 : A) : (term446 A B t _55484 f s _55485) = (term446 A B t _55484 f s _55485).
Proof. exact (eq_refl (term446 A B t _55484 f s _55485)). Qed.
Lemma lem4619941 {A B : Type'} (t : B -> Prop) (_55484 : B) (f : A -> B) (s : A -> Prop) (_55485 : A) : ((term429 A B f s _55485 t _55484) = (term446 A B t _55484 f s _55485)) = ((term446 A B t _55484 f s _55485) = (term446 A B t _55484 f s _55485)).
Proof. exact (MK_COMB (@lem4619922 A B t _55484 f s _55485) (@lem4619940 A B t _55484 f s _55485)). Qed.
Lemma lem4619943 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4619944 (x : Prop) : (x = x) = True.
Proof. exact (@lem4619943 Prop x). Qed.
Lemma lem4619945 {A B : Type'} (t : B -> Prop) (_55484 : B) (f : A -> B) (s : A -> Prop) (_55485 : A) : ((term446 A B t _55484 f s _55485) = (term446 A B t _55484 f s _55485)) = True.
Proof. exact (@lem4619944 (term446 A B t _55484 f s _55485)). Qed.
Lemma lem4619946 {A B : Type'} (t : B -> Prop) (_55484 : B) (f : A -> B) (s : A -> Prop) (_55485 : A) : ((term429 A B f s _55485 t _55484) = (term446 A B t _55484 f s _55485)) = True.
Proof. exact (TRANS (@lem4619941 A B t _55484 f s _55485) (@lem4619945 A B t _55484 f s _55485)). Qed.
Lemma lem4619947 {A B : Type'} (t : B -> Prop) (_55484 : B) (f : A -> B) (s : A -> Prop) (_55485 : A) : True = ((term429 A B f s _55485 t _55484) = (term446 A B t _55484 f s _55485)).
Proof. exact (SYM (@lem4619946 A B t _55484 f s _55485)). Qed.
Lemma lem4619948 {A B : Type'} (t : B -> Prop) (_55484 : B) (f : A -> B) (s : A -> Prop) (_55485 : A) : (term429 A B f s _55485 t _55484) = (term446 A B t _55484 f s _55485).
Proof. exact (EQ_MP (@lem4619947 A B t _55484 f s _55485) (@lem0)). Qed.
Lemma lem4619949 {A B : Type'} (_55484 : B) (_55485 : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term446 A B t _55484 f s _55485.
Proof. exact (EQ_MP (@lem4619948 A B t _55484 f s _55485) (@lem4619556 A B _55485 _55484 k f t s h1)). Qed.
Lemma lem4619951 (b : Prop) (a : Prop) : (a \/ b) = (term435 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4619952 {A B : Type'} (f : A -> B) (s : A -> Prop) (_55485 : A) (t : B -> Prop) (_55484 : B) : (term446 A B t _55484 f s _55485) = (term449 A B f s _55485 t _55484).
Proof. exact (@lem4619951 (term387 A B _55484 f s _55485) (@I (B -> Prop) t _55484)). Qed.
Lemma lem4619954 (a : Prop) (b : Prop) : (term450 a b) = (term451 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4619955 {A B : Type'} (_55484 : B) (f : A -> B) (s : A -> Prop) (_55485 : A) : (term452 A B _55484 f s _55485) = (term453 A B _55484 f s _55485).
Proof. exact (@lem4619954 (term430 A B _55484 f _55485) (term385 A s _55485)). Qed.
Lemma lem4619957 (a : Prop) : (term336 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4619958 {A B : Type'} (_55484 : B) (f : A -> B) (_55485 : A) : (term454 A B _55484 f _55485) = (_55484 = (f _55485)).
Proof. exact (@lem4619957 (_55484 = (f _55485))). Qed.
Lemma lem4619959 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4619960 {A B : Type'} (_55484 : B) (f : A -> B) (_55485 : A) : (term455 A B _55484 f _55485) = (term303 A B _55484 f _55485).
Proof. exact (MK_COMB (@lem4619959) (@lem4619958 A B _55484 f _55485)). Qed.
Lemma lem4619962 (a : Prop) : (term336 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4619963 {A : Type'} (s : A -> Prop) (_55485 : A) : (term456 A s _55485) = (@I (A -> Prop) s _55485).
Proof. exact (@lem4619962 (@I (A -> Prop) s _55485)). Qed.
Lemma lem4619964 {A B : Type'} (_55484 : B) (f : A -> B) (s : A -> Prop) (_55485 : A) : (term453 A B _55484 f s _55485) = (term457 A B _55484 f s _55485).
Proof. exact (MK_COMB (@lem4619960 A B _55484 f _55485) (@lem4619963 A s _55485)). Qed.
Lemma lem4619965 {A B : Type'} (_55484 : B) (f : A -> B) (s : A -> Prop) (_55485 : A) : (term452 A B _55484 f s _55485) = (term457 A B _55484 f s _55485).
Proof. exact (TRANS (@lem4619955 A B _55484 f s _55485) (@lem4619964 A B _55484 f s _55485)). Qed.
Lemma lem4619966 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4619967 {A B : Type'} (_55484 : B) (f : A -> B) (s : A -> Prop) (_55485 : A) : (term458 A B _55484 f s _55485) = (term459 A B _55484 f s _55485).
Proof. exact (MK_COMB (@lem4619966) (@lem4619965 A B _55484 f s _55485)). Qed.
Lemma lem4619968 {B : Type'} (t : B -> Prop) (_55484 : B) : (@I (B -> Prop) t _55484) = (@I (B -> Prop) t _55484).
Proof. exact (eq_refl (@I (B -> Prop) t _55484)). Qed.
Lemma lem4619969 {A B : Type'} (f : A -> B) (s : A -> Prop) (_55485 : A) (t : B -> Prop) (_55484 : B) : (term449 A B f s _55485 t _55484) = (term460 A B f s _55485 t _55484).
Proof. exact (MK_COMB (@lem4619967 A B _55484 f s _55485) (@lem4619968 B t _55484)). Qed.
Lemma lem4619970 {A B : Type'} (f : A -> B) (s : A -> Prop) (_55485 : A) (t : B -> Prop) (_55484 : B) : (term446 A B t _55484 f s _55485) = (term460 A B f s _55485 t _55484).
Proof. exact (TRANS (@lem4619952 A B f s _55485 t _55484) (@lem4619969 A B f s _55485 t _55484)). Qed.
Lemma lem4619972 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term318 A B k f t s) : term461 A B f s x.
Proof. exact (conj (@lem4619815 A B f x) (@lem4619871 A B x k f t s h1 h2)). Qed.
Lemma lem4619974 {A B : Type'} (_55485 : A) (_55484 : B) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term460 A B f s _55485 t _55484.
Proof. exact (EQ_MP (@lem4619970 A B f s _55485 t _55484) (@lem4619949 A B _55484 _55485 k f t s h1)). Qed.
Lemma lem4619975 {A B : Type'} (_55485 : A) (_55484 : B) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term460 A B f s _55485 t _55484.
Proof. exact (@lem4619974 A B _55485 _55484 k f t s h1). Qed.
Lemma lem4619976 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term462 A B s t f x.
Proof. exact (@lem4619975 A B x (f x) k f t s h1). Qed.
Lemma lem4619979 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term318 A B k f t s) : term401 A B t f x.
Proof. exact (@lem4619976 A B x k f t s h2 (@lem4619972 A B x k f t s h1 h2)). Qed.
Lemma lem4619980 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term318 A B k f t s) : term463 A B t f x.
Proof. exact (fun h0 : term403 A B t f x => @lem4619979 A B x k f t s h1 h2). Qed.
Lemma lem4619982 (p : Prop) : (term438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4619983 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) : (term463 A B t f x) = (term401 A B t f x).
Proof. exact (@lem4619982 (term401 A B t f x)). Qed.
Lemma lem4619984 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term318 A B k f t s) : term401 A B t f x.
Proof. exact (EQ_MP (@lem4619983 A B t f x) (@lem4619980 A B x k f t s h1 h2)). Qed.
Lemma lem4619987 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4619989 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) : (term403 A B t f x) = (term464 A B t f x).
Proof. exact (@lem4619987 (term401 A B t f x)). Qed.
Lemma lem4619992 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) (h1 : term403 A B t f x) : term464 A B t f x.
Proof. exact (EQ_MP (@lem4619989 A B t f x) (@lem4619562 A B t f x h1)). Qed.
Lemma lem4619995 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term403 A B t f x) (h3 : term318 A B k f t s) : False.
Proof. exact (@lem4619992 A B t f x h2 (@lem4619984 A B x k f t s h1 h3)). Qed.
Lemma lem4619996 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term403 A B t f x) (h3 : term318 A B k f t s) : term440.
Proof. exact (fun h0 : ~ False => @lem4619995 A B x k f t s h1 h2 h3). Qed.
Lemma lem4619998 (p : Prop) : (term438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4619999 : term440 = False.
Proof. exact (@lem4619998 False). Qed.
Lemma lem4620000 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term403 A B t f x) (h3 : term318 A B k f t s) : False.
Proof. exact (EQ_MP (@lem4619999) (@lem4619996 A B x k f t s h1 h2 h3)). Qed.
Lemma lem4620001 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term403 A B t f x) (h3 : term318 A B k f t s) : (term403 A B t f x) = False.
Proof. exact (prop_ext (fun h4 : term403 A B t f x => @lem4620000 A B x k f t s h1 h2 h3) (fun h4 : False => @lem4619562 A B t f x h2)). Qed.
Lemma lem4620002 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term403 A B t f x) (h3 : term318 A B k f t s) : False.
Proof. exact (EQ_MP (@lem4620001 A B x k f t s h1 h2 h3) (@lem4619562 A B t f x h2)). Qed.
Lemma lem4620003 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term403 A B t f x) (h3 : term318 A B k f t s) : (term2 A B f k x) = False.
Proof. exact (prop_ext (fun h4 : term2 A B f k x => @lem4620002 A B x k f t s h1 h2 h3) (fun h4 : False => @lem4619538 A B f k x h1)). Qed.
Lemma lem4620004 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term403 A B t f x) (h3 : term318 A B k f t s) : False.
Proof. exact (EQ_MP (@lem4620003 A B x k f t s h1 h2 h3) (@lem4619538 A B f k x h1)). Qed.
Lemma lem4620005 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term385 A s x) (h3 : term318 A B k f t s) : (term385 A s x) = False.
Proof. exact (prop_ext (fun h4 : term385 A s x => @lem4619720 A B x k f t s h1 h2 h3) (fun h4 : False => @lem4619536 A s x h2)). Qed.
Lemma lem4620006 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term385 A s x) (h3 : term318 A B k f t s) : False.
Proof. exact (EQ_MP (@lem4620005 A B x k f t s h1 h2 h3) (@lem4619536 A s x h2)). Qed.
Lemma lem4620007 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term385 A s x) (h3 : term318 A B k f t s) : (term2 A B f k x) = False.
Proof. exact (prop_ext (fun h4 : term2 A B f k x => @lem4620006 A B x k f t s h1 h2 h3) (fun h4 : False => @lem4619512 A B f k x h1)). Qed.
Lemma lem4620008 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term385 A s x) (h3 : term318 A B k f t s) : False.
Proof. exact (EQ_MP (@lem4620007 A B x k f t s h1 h2 h3) (@lem4619512 A B f k x h1)). Qed.
Lemma lem4620009 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term403 A B t f x) (h3 : term318 A B k f t s) : (term403 A B t f x) = False.
Proof. exact (prop_ext (fun h4 : term403 A B t f x => @lem4620004 A B x k f t s h1 h2 h3) (fun h4 : False => @lem4619492 A B t f x h2)). Qed.
Lemma lem4620010 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term403 A B t f x) (h3 : term318 A B k f t s) : False.
Proof. exact (EQ_MP (@lem4620009 A B x k f t s h1 h2 h3) (@lem4619492 A B t f x h2)). Qed.
Lemma lem4620011 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term403 A B t f x) (h3 : term318 A B k f t s) : (term2 A B f k x) = False.
Proof. exact (prop_ext (fun h4 : term2 A B f k x => @lem4620010 A B x k f t s h1 h2 h3) (fun h4 : False => @lem4619419 A B f k x h1)). Qed.
Lemma lem4620012 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term403 A B t f x) (h3 : term318 A B k f t s) : False.
Proof. exact (EQ_MP (@lem4620011 A B x k f t s h1 h2 h3) (@lem4619419 A B f k x h1)). Qed.
Lemma lem4620013 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term385 A s x) (h3 : term318 A B k f t s) : (term385 A s x) = False.
Proof. exact (prop_ext (fun h4 : term385 A s x => @lem4620008 A B x k f t s h1 h2 h3) (fun h4 : False => @lem4619415 A s x h2)). Qed.
Lemma lem4620014 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term385 A s x) (h3 : term318 A B k f t s) : False.
Proof. exact (EQ_MP (@lem4620013 A B x k f t s h1 h2 h3) (@lem4619415 A s x h2)). Qed.
Lemma lem4620015 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term385 A s x) (h3 : term318 A B k f t s) : (term2 A B f k x) = False.
Proof. exact (prop_ext (fun h4 : term2 A B f k x => @lem4620014 A B x k f t s h1 h2 h3) (fun h4 : False => @lem4619342 A B f k x h1)). Qed.
Lemma lem4620016 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term385 A s x) (h3 : term318 A B k f t s) : False.
Proof. exact (EQ_MP (@lem4620015 A B x k f t s h1 h2 h3) (@lem4619342 A B f k x h1)). Qed.
Lemma lem4620017 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term403 A B t f x) (h3 : term318 A B k f t s) : (term403 A B t f x) = False.
Proof. exact (prop_ext (fun h4 : term403 A B t f x => @lem4620012 A B x k f t s h1 h2 h3) (fun h4 : False => @lem4619492 A B t f x h2)). Qed.
Lemma lem4620018 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term403 A B t f x) (h3 : term318 A B k f t s) : False.
Proof. exact (EQ_MP (@lem4620017 A B x k f t s h1 h2 h3) (@lem4619492 A B t f x h2)). Qed.
Lemma lem4620019 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term403 A B t f x) (h3 : term318 A B k f t s) : (term2 A B f k x) = False.
Proof. exact (prop_ext (fun h4 : term2 A B f k x => @lem4620018 A B x k f t s h1 h2 h3) (fun h4 : False => @lem4619419 A B f k x h1)). Qed.
Lemma lem4620020 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term403 A B t f x) (h3 : term318 A B k f t s) : False.
Proof. exact (EQ_MP (@lem4620019 A B x k f t s h1 h2 h3) (@lem4619419 A B f k x h1)). Qed.
Lemma lem4620021 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term385 A s x) (h3 : term318 A B k f t s) : (term385 A s x) = False.
Proof. exact (prop_ext (fun h4 : term385 A s x => @lem4620016 A B x k f t s h1 h2 h3) (fun h4 : False => @lem4619415 A s x h2)). Qed.
Lemma lem4620022 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term385 A s x) (h3 : term318 A B k f t s) : False.
Proof. exact (EQ_MP (@lem4620021 A B x k f t s h1 h2 h3) (@lem4619415 A s x h2)). Qed.
Lemma lem4620023 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term385 A s x) (h3 : term318 A B k f t s) : (term2 A B f k x) = False.
Proof. exact (prop_ext (fun h4 : term2 A B f k x => @lem4620022 A B x k f t s h1 h2 h3) (fun h4 : False => @lem4619342 A B f k x h1)). Qed.
Lemma lem4620024 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term385 A s x) (h3 : term318 A B k f t s) : False.
Proof. exact (EQ_MP (@lem4620023 A B x k f t s h1 h2 h3) (@lem4619342 A B f k x h1)). Qed.
Lemma lem4620025 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term354 A B s t f x) (h2 : term2 A B f k x) (h3 : term318 A B k f t s) : False.
Proof. exact (or_elim (@lem4619330 A B s t f x h1) (fun h0 : term385 A s x => @lem4620024 A B x k f t s h2 h0 h3) (fun h0 : term403 A B t f x => @lem4620020 A B x k f t s h2 h0 h3)). Qed.
Lemma lem4620026 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term354 A B s t f x) (h2 : term2 A B f k x) (h3 : term318 A B k f t s) : (term2 A B f k x) = False.
Proof. exact (prop_ext (fun h4 : term2 A B f k x => @lem4620025 A B x k f t s h1 h2 h3) (fun h4 : False => @lem4619304 A B f k x h2)). Qed.
Lemma lem4620027 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term354 A B s t f x) (h2 : term2 A B f k x) (h3 : term318 A B k f t s) : False.
Proof. exact (EQ_MP (@lem4620026 A B x k f t s h1 h2 h3) (@lem4619304 A B f k x h2)). Qed.
Lemma lem4620028 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term354 A B s t f x) (h2 : term2 A B f k x) (h3 : term318 A B k f t s) : (term2 A B f k x) = False.
Proof. exact (prop_ext (fun h4 : term2 A B f k x => @lem4620027 A B x k f t s h1 h2 h3) (fun h4 : False => @lem4619202 A B f k x h2)). Qed.
Lemma lem4620029 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term354 A B s t f x) (h2 : term2 A B f k x) (h3 : term318 A B k f t s) : False.
Proof. exact (EQ_MP (@lem4620028 A B x k f t s h1 h2 h3) (@lem4619202 A B f k x h2)). Qed.
Lemma lem4620030 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term354 A B s t f x) (h2 : term2 A B f k x) (h3 : term318 A B k f t s) : (term354 A B s t f x) = False.
Proof. exact (prop_ext (fun h4 : term354 A B s t f x => @lem4620029 A B x k f t s h1 h2 h3) (fun h4 : False => @lem4619030 A B s t f x h1)). Qed.
Lemma lem4620031 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term354 A B s t f x) (h2 : term2 A B f k x) (h3 : term318 A B k f t s) : False.
Proof. exact (EQ_MP (@lem4620030 A B x k f t s h1 h2 h3) (@lem4619030 A B s t f x h1)). Qed.
Lemma lem4620032 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term318 A B k f t s) : term353 A B s t f x.
Proof. exact (fun h0 : term354 A B s t f x => @lem4620031 A B x k f t s h0 h1 h2). Qed.
Lemma lem4620033 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term2 A B f k x) (h2 : term318 A B k f t s) : term324 A B s t f x.
Proof. exact (EQ_MP (@lem4619029 A B s t f x) (@lem4620032 A B x k f t s h1 h2)). Qed.
Lemma lem4620034 {A B : Type'} (x : A) (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term325 A B k s t f x.
Proof. exact (fun h0 : term2 A B f k x => @lem4620033 A B x k f t s h0 h1). Qed.
Lemma lem4620039 {A B : Type'} (k : A -> B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term318 A B k f t s) : term327 A B k s t f.
Proof. exact (fun x : A => @lem4620034 A B x k f t s h1). Qed.
Lemma lem4620040 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) : term328 A B k s t f.
Proof. exact (fun h0 : term318 A B k f t s => @lem4620039 A B k f t s h0). Qed.
Lemma lem4620045 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : term340 A B s t f.
Proof. exact (fun k : A -> B => @lem4620040 A B k s t f). Qed.
Lemma lem4620050 {A B : Type'} (t : B -> Prop) (f : A -> B) : term344 A B t f.
Proof. exact (fun s : A -> Prop => @lem4620045 A B s t f). Qed.
Lemma lem4620055 {A B : Type'} (f : A -> B) : term348 A B f.
Proof. exact (fun t : B -> Prop => @lem4620050 A B t f). Qed.
Lemma lem4620060 {A B : Type'} : term352 A B.
Proof. exact (fun f : A -> B => @lem4620055 A B f). Qed.
Lemma lem4620061 {A B : Type'} : term351 A B.
Proof. exact (EQ_MP (@lem4619023 A B) (@lem4620060 A B)). Qed.
Lemma lem4620062 {A B : Type'} (f : A -> B) : term465 A B f.
Proof. exact (@lem4620061 A B f). Qed.
Lemma lem4620063 {A B : Type'} (f : A -> B) : (term465 A B f) = (term347 A B f).
Proof. exact (eq_refl (term465 A B f)). Qed.
Lemma lem4620064 {A B : Type'} (f : A -> B) : term347 A B f.
Proof. exact (EQ_MP (@lem4620063 A B f) (@lem4620062 A B f)). Qed.
Lemma lem4620065 {A B : Type'} (f : A -> B) (t : B -> Prop) : term466 A B f t.
Proof. exact (@lem4620064 A B f t). Qed.
Lemma lem4620066 {A B : Type'} (t : B -> Prop) (f : A -> B) : (term466 A B f t) = (term343 A B t f).
Proof. exact (eq_refl (term466 A B f t)). Qed.
Lemma lem4620067 {A B : Type'} (t : B -> Prop) (f : A -> B) : term343 A B t f.
Proof. exact (EQ_MP (@lem4620066 A B t f) (@lem4620065 A B f t)). Qed.
Lemma lem4620068 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term467 A B t f s.
Proof. exact (@lem4620067 A B t f s). Qed.
Lemma lem4620069 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term467 A B t f s) = (term339 A B s t f).
Proof. exact (eq_refl (term467 A B t f s)). Qed.
Lemma lem4620070 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : term339 A B s t f.
Proof. exact (EQ_MP (@lem4620069 A B s t f) (@lem4620068 A B t f s)). Qed.
Lemma lem4620071 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (k : A -> B) : term468 A B s t f k.
Proof. exact (@lem4620070 A B s t f k). Qed.
Lemma lem4620072 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term468 A B s t f k) = (term330 A B k s t f).
Proof. exact (eq_refl (term468 A B s t f k)). Qed.
Lemma lem4620073 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) : term330 A B k s t f.
Proof. exact (EQ_MP (@lem4620072 A B k s t f) (@lem4620071 A B s t f k)). Qed.
Lemma lem4620075 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) : term330 A B k s t f.
Proof. exact (@lem4618771 A B k s t f (@lem4620073 A B k s t f)). Qed.
Lemma lem4620076 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term331 A B k s t f) : False.
Proof. exact (@lem4620075 A B k s t f (@lem4618755 A B k s t f h1)). Qed.
Lemma lem4620077 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term331 A B k s t f) : (term331 A B k s t f) = False.
Proof. exact (prop_ext (fun h2 : term331 A B k s t f => @lem4620076 A B k s t f h1) (fun h2 : False => @lem4618755 A B k s t f h1)). Qed.
Lemma lem4620078 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term331 A B k s t f) : False.
Proof. exact (EQ_MP (@lem4620077 A B k s t f h1) (@lem4618755 A B k s t f h1)). Qed.
Lemma lem4620079 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) : term330 A B k s t f.
Proof. exact (fun h0 : term331 A B k s t f => @lem4620078 A B k s t f h0). Qed.
Lemma lem4620080 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) : term328 A B k s t f.
Proof. exact (EQ_MP (@lem4618754 A B k s t f) (@lem4620079 A B k s t f)). Qed.
Lemma lem4620081 {A B : Type'} (k : A -> B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : term296 A B k s f t.
Proof. exact (EQ_MP (@lem4618750 A B k s f t) (@lem4620080 A B k s t f)). Qed.
Lemma lem4620082 {A B : Type'} (k : A -> B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : term295 A B k s f t.
Proof. exact (EQ_MP (@lem4618595 A B k s f t) (@lem4620081 A B k s f t)). Qed.
Lemma lem4620083 {A B : Type'} (k : A -> B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term177 A B f k s) (h4 : term178 A B f s t) : term274 A B k s f t.
Proof. exact (@lem4620082 A B k s f t (@lem4618529 A B k f s t h1 h2 h3 h4)). Qed.
Lemma lem4620084 {A B : Type'} (k : A -> B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term177 A B f k s) (h4 : term178 A B f s t) : term216 A B f k s t.
Proof. exact (EQ_MP (@lem4618516 A B f k s t) (@lem4620083 A B k f s t h1 h2 h3 h4)). Qed.
Lemma lem4620088 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term51 A B f g).
Proof. exact (EQ_MP (@lem4617780 A B f g) (@lem4617779 A B f g)). Qed.
Lemma lem4620089 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term51 A B f g).
Proof. exact (@lem4620088 A B f g). Qed.
Lemma lem4620090 {A B : Type'} (f : A -> B) (k : A -> B) : (f = (term469 A B f k)) = (term470 A B f k).
Proof. exact (@lem4620089 A B f (term469 A B f k)). Qed.
Lemma lem4620100 {A B : Type'} (f : A -> B) (y : A) : (term167 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4620101 {A B : Type'} (f : A -> B) (y : A) : (term167 A B f y) = (f y).
Proof. exact (@lem4620100 A B f y). Qed.
Lemma lem4620102 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term471 A B f k x) = (term472 A B f k x).
Proof. exact (@lem4620101 A B (term469 A B f k) x). Qed.
Lemma lem4620103 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term472 A B f k x) = (term473 A B f k x).
Proof. exact (eq_refl (term472 A B f k x)). Qed.
Lemma lem4620104 {A B : Type'} (f : A -> B) (k : A -> B) : (term474 A B f k) = (term469 A B f k).
Proof. exact (fun_ext (fun x : A => @lem4620103 A B f k x)). Qed.
Lemma lem4620105 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4620106 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term471 A B f k x) = (term472 A B f k x).
Proof. exact (MK_COMB (@lem4620104 A B f k) (@lem4620105 A x)). Qed.
Lemma lem4620107 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4620108 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term475 A B f k x) = (term476 A B f k x).
Proof. exact (MK_COMB (@lem4620107 B) (@lem4620106 A B f k x)). Qed.
Lemma lem4620109 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term472 A B f k x) = (term473 A B f k x).
Proof. exact (eq_refl (term472 A B f k x)). Qed.
Lemma lem4620110 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : ((term471 A B f k x) = (term472 A B f k x)) = ((term472 A B f k x) = (term473 A B f k x)).
Proof. exact (MK_COMB (@lem4620108 A B f k x) (@lem4620109 A B f k x)). Qed.
Lemma lem4620111 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term472 A B f k x) = (term473 A B f k x).
Proof. exact (EQ_MP (@lem4620110 A B f k x) (@lem4620102 A B f k x)). Qed.
Lemma lem4620132 {A B : Type'} (f : A -> B) (x : A) : (term477 A B f x) = (term477 A B f x).
Proof. exact (eq_refl (term477 A B f x)). Qed.
Lemma lem4620133 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : ((f x) = (term472 A B f k x)) = ((f x) = (term473 A B f k x)).
Proof. exact (MK_COMB (@lem4620132 A B f x) (@lem4620111 A B f k x)). Qed.
Lemma lem4620138 {A B : Type'} (f : A -> B) (k : A -> B) : (term478 A B f k) = (term479 A B f k).
Proof. exact (fun_ext (fun x : A => @lem4620133 A B f k x)). Qed.
Lemma lem4620139 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4620140 {A B : Type'} (f : A -> B) (k : A -> B) : (term470 A B f k) = (term480 A B f k).
Proof. exact (MK_COMB (@lem4620139 A) (@lem4620138 A B f k)). Qed.
Lemma lem4620145 {A B : Type'} (f : A -> B) (k : A -> B) : (f = (term469 A B f k)) = (term480 A B f k).
Proof. exact (TRANS (@lem4620090 A B f k) (@lem4620140 A B f k)). Qed.
Lemma lem4620146 {A B : Type'} (f : A -> B) (k : A -> B) : (term480 A B f k) = (f = (term469 A B f k)).
Proof. exact (SYM (@lem4620145 A B f k)). Qed.
Lemma lem4620154 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term46 A B y f s) = (term47 A B y f s).
Proof. exact (EQ_MP (@lem4617774 A B y f s) (@lem4617773 A B y s f)). Qed.
Lemma lem4620155 {A B : Type'} (y : prod A B) (f : type1428 A B) (s : A -> Prop) : (term481 A B y f s) = (term482 A B y f s).
Proof. exact (@lem4620154 A (prod A B) y f s). Qed.
Lemma lem4620156 {A B : Type'} (x : A) (y : B) (f : A -> B) (k : A -> B) : (term483 A B x y f k) = (term484 A B x y f k).
Proof. exact (@lem4620155 A B (@pair A B x y) (term225 A B f) (term223 A B f k)). Qed.
Lemma lem4620166 {A B : Type'} (f : A -> B) (y : A) : (term167 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4620167 {A B : Type'} (f : type1428 A B) (y : A) : (term261 A B f y) = (f y).
Proof. exact (@lem4620166 A (prod A B) f y). Qed.
Lemma lem4620168 {A B : Type'} (f : A -> B) (x' : A) : (term262 A B f x') = (term263 A B f x').
Proof. exact (@lem4620167 A B (term225 A B f) x'). Qed.
Lemma lem4620169 {A B : Type'} (f : A -> B) (x : A) : (term263 A B f x) = (term264 A B f x).
Proof. exact (eq_refl (term263 A B f x)). Qed.
Lemma lem4620170 {A B : Type'} (f : A -> B) : (term265 A B f) = (term225 A B f).
Proof. exact (fun_ext (fun x : A => @lem4620169 A B f x)). Qed.
Lemma lem4620171 {A : Type'} (x' : A) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem4620172 {A B : Type'} (f : A -> B) (x' : A) : (term262 A B f x') = (term263 A B f x').
Proof. exact (MK_COMB (@lem4620170 A B f) (@lem4620171 A x')). Qed.
Lemma lem4620173 {A B : Type'} : (@eq (prod A B)) = (@eq (prod A B)).
Proof. exact (eq_refl (@eq (prod A B))). Qed.
Lemma lem4620174 {A B : Type'} (f : A -> B) (x' : A) : (term266 A B f x') = (term267 A B f x').
Proof. exact (MK_COMB (@lem4620173 A B) (@lem4620172 A B f x')). Qed.
Lemma lem4620175 {A B : Type'} (f : A -> B) (x' : A) : (term263 A B f x') = (term264 A B f x').
Proof. exact (eq_refl (term263 A B f x')). Qed.
Lemma lem4620176 {A B : Type'} (f : A -> B) (x' : A) : ((term262 A B f x') = (term263 A B f x')) = ((term263 A B f x') = (term264 A B f x')).
Proof. exact (MK_COMB (@lem4620174 A B f x') (@lem4620175 A B f x')). Qed.
Lemma lem4620177 {A B : Type'} (f : A -> B) (x' : A) : (term263 A B f x') = (term264 A B f x').
Proof. exact (EQ_MP (@lem4620176 A B f x') (@lem4620168 A B f x')). Qed.
Lemma lem4620178 {A B : Type'} (x : A) (y : B) : (term485 A B x y) = (term485 A B x y).
Proof. exact (eq_refl (term485 A B x y)). Qed.
Lemma lem4620179 {A B : Type'} (x : A) (y : B) (f : A -> B) (x' : A) : ((@pair A B x y) = (term263 A B f x')) = ((@pair A B x y) = (term264 A B f x')).
Proof. exact (MK_COMB (@lem4620178 A B x y) (@lem4620177 A B f x')). Qed.
Lemma lem4620181 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : ((@pair A B x y) = (@pair A B a b)) = (term35 A B x a y b).
Proof. exact (EQ_MP (@lem4617727 A B x a y b) (@lem4617726 A B x a y b)). Qed.
Lemma lem4620182 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : ((@pair A B x y) = (@pair A B a b)) = (term35 A B x a y b).
Proof. exact (@lem4620181 A B x a y b). Qed.
Lemma lem4620183 {A B : Type'} (x : A) (y : B) (f : A -> B) (x' : A) : ((@pair A B x y) = (term264 A B f x')) = (term486 A B x y f x').
Proof. exact (@lem4620182 A B x x' y (f x')). Qed.
Lemma lem4620190 {A B : Type'} (x : A) (y : B) (f : A -> B) (x' : A) : ((@pair A B x y) = (term263 A B f x')) = (term486 A B x y f x').
Proof. exact (TRANS (@lem4620179 A B x y f x') (@lem4620183 A B x y f x')). Qed.
Lemma lem4620191 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4620192 {A B : Type'} (x : A) (y : B) (f : A -> B) (x' : A) : (term487 A B x y f x') = (term488 A B x y f x').
Proof. exact (MK_COMB (@lem4620191) (@lem4620190 A B x y f x')). Qed.
Lemma lem4620194 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term40 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4617758 _83095 p x) (@lem4617757 _83095 p x)). Qed.
Lemma lem4620195 {A : Type'} (p : A -> Prop) (x : A) : (term40 A x p) = (p x).
Proof. exact (@lem4620194 A p x). Qed.
Lemma lem4620196 {A B : Type'} (f : A -> B) (k : A -> B) (x' : A) : (term243 A B x' f k) = (term244 A B f k x').
Proof. exact (@lem4620195 A (term245 A B f k) x'). Qed.
Lemma lem4620197 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term244 A B f k x) = (term2 A B f k x).
Proof. exact (eq_refl (term244 A B f k x)). Qed.
Lemma lem4620198 {A : Type'} (GEN_PVAR_175 : A) : (@SETSPEC A GEN_PVAR_175) = (@SETSPEC A GEN_PVAR_175).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_175)). Qed.
Lemma lem4620199 {A B : Type'} (GEN_PVAR_175 : A) (f : A -> B) (k : A -> B) (x : A) : (term246 A B GEN_PVAR_175 f k x) = (term247 A B GEN_PVAR_175 f k x).
Proof. exact (MK_COMB (@lem4620198 A GEN_PVAR_175) (@lem4620197 A B f k x)). Qed.
Lemma lem4620200 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4620201 {A B : Type'} (GEN_PVAR_175 : A) (f : A -> B) (k : A -> B) (x : A) : (term248 A B GEN_PVAR_175 f k x) = (term249 A B GEN_PVAR_175 f k x).
Proof. exact (MK_COMB (@lem4620199 A B GEN_PVAR_175 f k x) (@lem4620200 A x)). Qed.
Lemma lem4620202 {A B : Type'} (GEN_PVAR_175 : A) (f : A -> B) (k : A -> B) : (term250 A B GEN_PVAR_175 f k) = (term251 A B GEN_PVAR_175 f k).
Proof. exact (fun_ext (fun x : A => @lem4620201 A B GEN_PVAR_175 f k x)). Qed.
Lemma lem4620203 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4620204 {A B : Type'} (GEN_PVAR_175 : A) (f : A -> B) (k : A -> B) : (term252 A B GEN_PVAR_175 f k) = (term253 A B GEN_PVAR_175 f k).
Proof. exact (MK_COMB (@lem4620203 A) (@lem4620202 A B GEN_PVAR_175 f k)). Qed.
Lemma lem4620205 {A B : Type'} (f : A -> B) (k : A -> B) : (term254 A B f k) = (term255 A B f k).
Proof. exact (fun_ext (fun GEN_PVAR_175 : A => @lem4620204 A B GEN_PVAR_175 f k)). Qed.
Lemma lem4620206 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4620207 {A B : Type'} (f : A -> B) (k : A -> B) : (term256 A B f k) = (term223 A B f k).
Proof. exact (MK_COMB (@lem4620206 A) (@lem4620205 A B f k)). Qed.
Lemma lem4620208 {A : Type'} (x' : A) : (@IN A x') = (@IN A x').
Proof. exact (eq_refl (@IN A x')). Qed.
Lemma lem4620209 {A B : Type'} (x' : A) (f : A -> B) (k : A -> B) : (term243 A B x' f k) = (term257 A B x' f k).
Proof. exact (MK_COMB (@lem4620208 A x') (@lem4620207 A B f k)). Qed.
Lemma lem4620210 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4620211 {A B : Type'} (x' : A) (f : A -> B) (k : A -> B) : (term258 A B x' f k) = (term259 A B x' f k).
Proof. exact (MK_COMB (@lem4620210) (@lem4620209 A B x' f k)). Qed.
Lemma lem4620212 {A B : Type'} (f : A -> B) (k : A -> B) (x' : A) : (term244 A B f k x') = (term2 A B f k x').
Proof. exact (eq_refl (term244 A B f k x')). Qed.
Lemma lem4620213 {A B : Type'} (f : A -> B) (k : A -> B) (x' : A) : ((term243 A B x' f k) = (term244 A B f k x')) = ((term257 A B x' f k) = (term2 A B f k x')).
Proof. exact (MK_COMB (@lem4620211 A B x' f k) (@lem4620212 A B f k x')). Qed.
Lemma lem4620214 {A B : Type'} (f : A -> B) (k : A -> B) (x' : A) : (term257 A B x' f k) = (term2 A B f k x').
Proof. exact (EQ_MP (@lem4620213 A B f k x') (@lem4620196 A B f k x')). Qed.
Lemma lem4620217 {A B : Type'} (x : A) (y : B) (f : A -> B) (k : A -> B) (x' : A) : (term489 A B x y x' f k) = (term490 A B x y f k x').
Proof. exact (MK_COMB (@lem4620192 A B x y f x') (@lem4620214 A B f k x')). Qed.
Lemma lem4620220 {A B : Type'} (x : A) (y : B) (f : A -> B) (k : A -> B) : (term491 A B x y f k) = (term492 A B x y f k).
Proof. exact (fun_ext (fun x' : A => @lem4620217 A B x y f k x')). Qed.
Lemma lem4620221 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4620222 {A B : Type'} (x : A) (y : B) (f : A -> B) (k : A -> B) : (term484 A B x y f k) = (term493 A B x y f k).
Proof. exact (MK_COMB (@lem4620221 A) (@lem4620220 A B x y f k)). Qed.
Lemma lem4620227 {A B : Type'} (x : A) (y : B) (f : A -> B) (k : A -> B) : (term483 A B x y f k) = (term493 A B x y f k).
Proof. exact (TRANS (@lem4620156 A B x y f k) (@lem4620222 A B x y f k)). Qed.
Lemma lem4620228 {A B : Type'} (x : A) (f : A -> B) (k : A -> B) : (term494 A B x f k) = (term495 A B x f k).
Proof. exact (fun_ext (fun y : B => @lem4620227 A B x y f k)). Qed.
Lemma lem4620229 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4620230 {A B : Type'} (x : A) (f : A -> B) (k : A -> B) : (term496 A B x f k) = (term497 A B x f k).
Proof. exact (MK_COMB (@lem4620229 B) (@lem4620228 A B x f k)). Qed.
Lemma lem4620235 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem4620236 {A B : Type'} (x : A) (f : A -> B) (k : A -> B) : (term498 A B x f k) = (term499 A B x f k).
Proof. exact (MK_COMB (@lem4620235 B) (@lem4620230 A B x f k)). Qed.
Lemma lem4620238 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term46 A B y f s) = (term47 A B y f s).
Proof. exact (EQ_MP (@lem4617774 A B y f s) (@lem4617773 A B y s f)). Qed.
Lemma lem4620239 {A B : Type'} (y : prod A B) (f : type1428 A B) (s : A -> Prop) : (term481 A B y f s) = (term482 A B y f s).
Proof. exact (@lem4620238 A (prod A B) y f s). Qed.
Lemma lem4620240 {A B : Type'} (x : A) (y : B) (f : A -> B) (k : A -> B) : (term483 A B x y f k) = (term484 A B x y f k).
Proof. exact (@lem4620239 A B (@pair A B x y) (term225 A B f) (term223 A B f k)). Qed.
Lemma lem4620250 {A B : Type'} (f : A -> B) (y : A) : (term167 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4620251 {A B : Type'} (f : type1428 A B) (y : A) : (term261 A B f y) = (f y).
Proof. exact (@lem4620250 A (prod A B) f y). Qed.
Lemma lem4620252 {A B : Type'} (f : A -> B) (x' : A) : (term262 A B f x') = (term263 A B f x').
Proof. exact (@lem4620251 A B (term225 A B f) x'). Qed.
Lemma lem4620253 {A B : Type'} (f : A -> B) (x : A) : (term263 A B f x) = (term264 A B f x).
Proof. exact (eq_refl (term263 A B f x)). Qed.
Lemma lem4620254 {A B : Type'} (f : A -> B) : (term265 A B f) = (term225 A B f).
Proof. exact (fun_ext (fun x : A => @lem4620253 A B f x)). Qed.
Lemma lem4620255 {A : Type'} (x' : A) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem4620256 {A B : Type'} (f : A -> B) (x' : A) : (term262 A B f x') = (term263 A B f x').
Proof. exact (MK_COMB (@lem4620254 A B f) (@lem4620255 A x')). Qed.
Lemma lem4620257 {A B : Type'} : (@eq (prod A B)) = (@eq (prod A B)).
Proof. exact (eq_refl (@eq (prod A B))). Qed.
Lemma lem4620258 {A B : Type'} (f : A -> B) (x' : A) : (term266 A B f x') = (term267 A B f x').
Proof. exact (MK_COMB (@lem4620257 A B) (@lem4620256 A B f x')). Qed.
Lemma lem4620259 {A B : Type'} (f : A -> B) (x' : A) : (term263 A B f x') = (term264 A B f x').
Proof. exact (eq_refl (term263 A B f x')). Qed.
Lemma lem4620260 {A B : Type'} (f : A -> B) (x' : A) : ((term262 A B f x') = (term263 A B f x')) = ((term263 A B f x') = (term264 A B f x')).
Proof. exact (MK_COMB (@lem4620258 A B f x') (@lem4620259 A B f x')). Qed.
Lemma lem4620261 {A B : Type'} (f : A -> B) (x' : A) : (term263 A B f x') = (term264 A B f x').
Proof. exact (EQ_MP (@lem4620260 A B f x') (@lem4620252 A B f x')). Qed.
Lemma lem4620262 {A B : Type'} (x : A) (y : B) : (term485 A B x y) = (term485 A B x y).
Proof. exact (eq_refl (term485 A B x y)). Qed.
Lemma lem4620263 {A B : Type'} (x : A) (y : B) (f : A -> B) (x' : A) : ((@pair A B x y) = (term263 A B f x')) = ((@pair A B x y) = (term264 A B f x')).
Proof. exact (MK_COMB (@lem4620262 A B x y) (@lem4620261 A B f x')). Qed.
Lemma lem4620265 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : ((@pair A B x y) = (@pair A B a b)) = (term35 A B x a y b).
Proof. exact (EQ_MP (@lem4617727 A B x a y b) (@lem4617726 A B x a y b)). Qed.
Lemma lem4620266 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : ((@pair A B x y) = (@pair A B a b)) = (term35 A B x a y b).
Proof. exact (@lem4620265 A B x a y b). Qed.
Lemma lem4620267 {A B : Type'} (x : A) (y : B) (f : A -> B) (x' : A) : ((@pair A B x y) = (term264 A B f x')) = (term486 A B x y f x').
Proof. exact (@lem4620266 A B x x' y (f x')). Qed.
Lemma lem4620274 {A B : Type'} (x : A) (y : B) (f : A -> B) (x' : A) : ((@pair A B x y) = (term263 A B f x')) = (term486 A B x y f x').
Proof. exact (TRANS (@lem4620263 A B x y f x') (@lem4620267 A B x y f x')). Qed.
Lemma lem4620275 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4620276 {A B : Type'} (x : A) (y : B) (f : A -> B) (x' : A) : (term487 A B x y f x') = (term488 A B x y f x').
Proof. exact (MK_COMB (@lem4620275) (@lem4620274 A B x y f x')). Qed.
Lemma lem4620278 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term40 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4617758 _83095 p x) (@lem4617757 _83095 p x)). Qed.
Lemma lem4620279 {A : Type'} (p : A -> Prop) (x : A) : (term40 A x p) = (p x).
Proof. exact (@lem4620278 A p x). Qed.
Lemma lem4620280 {A B : Type'} (f : A -> B) (k : A -> B) (x' : A) : (term243 A B x' f k) = (term244 A B f k x').
Proof. exact (@lem4620279 A (term245 A B f k) x'). Qed.
Lemma lem4620281 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term244 A B f k x) = (term2 A B f k x).
Proof. exact (eq_refl (term244 A B f k x)). Qed.
Lemma lem4620282 {A : Type'} (GEN_PVAR_175 : A) : (@SETSPEC A GEN_PVAR_175) = (@SETSPEC A GEN_PVAR_175).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_175)). Qed.
Lemma lem4620283 {A B : Type'} (GEN_PVAR_175 : A) (f : A -> B) (k : A -> B) (x : A) : (term246 A B GEN_PVAR_175 f k x) = (term247 A B GEN_PVAR_175 f k x).
Proof. exact (MK_COMB (@lem4620282 A GEN_PVAR_175) (@lem4620281 A B f k x)). Qed.
Lemma lem4620284 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4620285 {A B : Type'} (GEN_PVAR_175 : A) (f : A -> B) (k : A -> B) (x : A) : (term248 A B GEN_PVAR_175 f k x) = (term249 A B GEN_PVAR_175 f k x).
Proof. exact (MK_COMB (@lem4620283 A B GEN_PVAR_175 f k x) (@lem4620284 A x)). Qed.
Lemma lem4620286 {A B : Type'} (GEN_PVAR_175 : A) (f : A -> B) (k : A -> B) : (term250 A B GEN_PVAR_175 f k) = (term251 A B GEN_PVAR_175 f k).
Proof. exact (fun_ext (fun x : A => @lem4620285 A B GEN_PVAR_175 f k x)). Qed.
Lemma lem4620287 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4620288 {A B : Type'} (GEN_PVAR_175 : A) (f : A -> B) (k : A -> B) : (term252 A B GEN_PVAR_175 f k) = (term253 A B GEN_PVAR_175 f k).
Proof. exact (MK_COMB (@lem4620287 A) (@lem4620286 A B GEN_PVAR_175 f k)). Qed.
Lemma lem4620289 {A B : Type'} (f : A -> B) (k : A -> B) : (term254 A B f k) = (term255 A B f k).
Proof. exact (fun_ext (fun GEN_PVAR_175 : A => @lem4620288 A B GEN_PVAR_175 f k)). Qed.
Lemma lem4620290 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4620291 {A B : Type'} (f : A -> B) (k : A -> B) : (term256 A B f k) = (term223 A B f k).
Proof. exact (MK_COMB (@lem4620290 A) (@lem4620289 A B f k)). Qed.
Lemma lem4620292 {A : Type'} (x' : A) : (@IN A x') = (@IN A x').
Proof. exact (eq_refl (@IN A x')). Qed.
Lemma lem4620293 {A B : Type'} (x' : A) (f : A -> B) (k : A -> B) : (term243 A B x' f k) = (term257 A B x' f k).
Proof. exact (MK_COMB (@lem4620292 A x') (@lem4620291 A B f k)). Qed.
Lemma lem4620294 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4620295 {A B : Type'} (x' : A) (f : A -> B) (k : A -> B) : (term258 A B x' f k) = (term259 A B x' f k).
Proof. exact (MK_COMB (@lem4620294) (@lem4620293 A B x' f k)). Qed.
Lemma lem4620296 {A B : Type'} (f : A -> B) (k : A -> B) (x' : A) : (term244 A B f k x') = (term2 A B f k x').
Proof. exact (eq_refl (term244 A B f k x')). Qed.
Lemma lem4620297 {A B : Type'} (f : A -> B) (k : A -> B) (x' : A) : ((term243 A B x' f k) = (term244 A B f k x')) = ((term257 A B x' f k) = (term2 A B f k x')).
Proof. exact (MK_COMB (@lem4620295 A B x' f k) (@lem4620296 A B f k x')). Qed.
Lemma lem4620298 {A B : Type'} (f : A -> B) (k : A -> B) (x' : A) : (term257 A B x' f k) = (term2 A B f k x').
Proof. exact (EQ_MP (@lem4620297 A B f k x') (@lem4620280 A B f k x')). Qed.
Lemma lem4620301 {A B : Type'} (x : A) (y : B) (f : A -> B) (k : A -> B) (x' : A) : (term489 A B x y x' f k) = (term490 A B x y f k x').
Proof. exact (MK_COMB (@lem4620276 A B x y f x') (@lem4620298 A B f k x')). Qed.
Lemma lem4620304 {A B : Type'} (x : A) (y : B) (f : A -> B) (k : A -> B) : (term491 A B x y f k) = (term492 A B x y f k).
Proof. exact (fun_ext (fun x' : A => @lem4620301 A B x y f k x')). Qed.
Lemma lem4620305 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4620306 {A B : Type'} (x : A) (y : B) (f : A -> B) (k : A -> B) : (term484 A B x y f k) = (term493 A B x y f k).
Proof. exact (MK_COMB (@lem4620305 A) (@lem4620304 A B x y f k)). Qed.
Lemma lem4620311 {A B : Type'} (x : A) (y : B) (f : A -> B) (k : A -> B) : (term483 A B x y f k) = (term493 A B x y f k).
Proof. exact (TRANS (@lem4620240 A B x y f k) (@lem4620306 A B x y f k)). Qed.
Lemma lem4620312 {A B : Type'} (x : A) (f : A -> B) (k : A -> B) : (term494 A B x f k) = (term495 A B x f k).
Proof. exact (fun_ext (fun y : B => @lem4620311 A B x y f k)). Qed.
Lemma lem4620313 {B : Type'} : (@ε B) = (@ε B).
Proof. exact (eq_refl (@ε B)). Qed.
Lemma lem4620314 {A B : Type'} (x : A) (f : A -> B) (k : A -> B) : (term500 A B x f k) = (term501 A B x f k).
Proof. exact (MK_COMB (@lem4620313 B) (@lem4620312 A B x f k)). Qed.
Lemma lem4620315 {A B : Type'} (x : A) (f : A -> B) (k : A -> B) : (term502 A B x f k) = (term503 A B x f k).
Proof. exact (MK_COMB (@lem4620236 A B x f k) (@lem4620314 A B x f k)). Qed.
Lemma lem4620316 {A B : Type'} (k : A -> B) (x : A) : (k x) = (k x).
Proof. exact (eq_refl (k x)). Qed.
Lemma lem4620317 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term473 A B f k x) = (term504 A B f k x).
Proof. exact (MK_COMB (@lem4620315 A B x f k) (@lem4620316 A B k x)). Qed.
Lemma lem4620318 {A B : Type'} (f : A -> B) (x : A) : (term477 A B f x) = (term477 A B f x).
Proof. exact (eq_refl (term477 A B f x)). Qed.
Lemma lem4620319 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : ((f x) = (term473 A B f k x)) = ((f x) = (term504 A B f k x)).
Proof. exact (MK_COMB (@lem4620318 A B f x) (@lem4620317 A B f k x)). Qed.
Lemma lem4620322 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : ((f x) = (term504 A B f k x)) = ((f x) = (term473 A B f k x)).
Proof. exact (SYM (@lem4620319 A B f k x)). Qed.
Lemma lem4620334 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = (term3 t1 t2 t3).
Proof. exact (EQ_MP (@lem4617715 t1 t2 t3) (@lem4617714 t1 t2 t3)). Qed.
Lemma lem4620335 {A B : Type'} (x : A) (y : B) (f : A -> B) (k : A -> B) (x' : A) : (term490 A B x y f k x') = (term505 A B x y f k x').
Proof. exact (@lem4620334 (x = x') (y = (f x')) (term2 A B f k x')). Qed.
Lemma lem4620346 {A B : Type'} (x : A) (y : B) (f : A -> B) (k : A -> B) : (term492 A B x y f k) = (term506 A B x y f k).
Proof. exact (fun_ext (fun x' : A => @lem4620335 A B x y f k x')). Qed.
Lemma lem4620347 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4620348 {A B : Type'} (x : A) (y : B) (f : A -> B) (k : A -> B) : (term493 A B x y f k) = (term507 A B x y f k).
Proof. exact (MK_COMB (@lem4620347 A) (@lem4620346 A B x y f k)). Qed.
Lemma lem4620352 {A : Type'} (P : A -> Prop) (a : A) : (term24 A a P) = (P a).
Proof. exact (EQ_MP (@lem4617706 A P a) (@lem4617705 A P a)). Qed.
Lemma lem4620353 {A : Type'} (P : A -> Prop) (a : A) : (term24 A a P) = (P a).
Proof. exact (@lem4620352 A P a). Qed.
Lemma lem4620354 {A B : Type'} (y : B) (f : A -> B) (k : A -> B) (x : A) : (term508 A B x y f k) = (term509 A B y f k x).
Proof. exact (@lem4620353 A (term510 A B y f k) x). Qed.
Lemma lem4620355 {A B : Type'} (y : B) (f : A -> B) (k : A -> B) (x' : A) : (term509 A B y f k x') = (term511 A B y f k x').
Proof. exact (eq_refl (term509 A B y f k x')). Qed.
Lemma lem4620356 {A : Type'} (x : A) (x' : A) : (term512 A x x') = (term512 A x x').
Proof. exact (eq_refl (term512 A x x')). Qed.
Lemma lem4620357 {A B : Type'} (x : A) (y : B) (f : A -> B) (k : A -> B) (x' : A) : (term513 A B x y f k x') = (term505 A B x y f k x').
Proof. exact (MK_COMB (@lem4620356 A x x') (@lem4620355 A B y f k x')). Qed.
Lemma lem4620358 {A B : Type'} (x : A) (y : B) (f : A -> B) (k : A -> B) : (term514 A B x y f k) = (term506 A B x y f k).
Proof. exact (fun_ext (fun x' : A => @lem4620357 A B x y f k x')). Qed.
Lemma lem4620359 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4620360 {A B : Type'} (x : A) (y : B) (f : A -> B) (k : A -> B) : (term508 A B x y f k) = (term507 A B x y f k).
Proof. exact (MK_COMB (@lem4620359 A) (@lem4620358 A B x y f k)). Qed.
Lemma lem4620361 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4620362 {A B : Type'} (x : A) (y : B) (f : A -> B) (k : A -> B) : (term515 A B x y f k) = (term516 A B x y f k).
Proof. exact (MK_COMB (@lem4620361) (@lem4620360 A B x y f k)). Qed.
Lemma lem4620363 {A B : Type'} (y : B) (f : A -> B) (k : A -> B) (x : A) : (term509 A B y f k x) = (term511 A B y f k x).
Proof. exact (eq_refl (term509 A B y f k x)). Qed.
Lemma lem4620364 {A B : Type'} (y : B) (f : A -> B) (k : A -> B) (x : A) : ((term508 A B x y f k) = (term509 A B y f k x)) = ((term507 A B x y f k) = (term511 A B y f k x)).
Proof. exact (MK_COMB (@lem4620362 A B x y f k) (@lem4620363 A B y f k x)). Qed.
Lemma lem4620365 {A B : Type'} (y : B) (f : A -> B) (k : A -> B) (x : A) : (term507 A B x y f k) = (term511 A B y f k x).
Proof. exact (EQ_MP (@lem4620364 A B y f k x) (@lem4620354 A B y f k x)). Qed.
Lemma lem4620372 {A B : Type'} (y : B) (f : A -> B) (k : A -> B) (x : A) : (term493 A B x y f k) = (term511 A B y f k x).
Proof. exact (TRANS (@lem4620348 A B x y f k) (@lem4620365 A B y f k x)). Qed.
Lemma lem4620373 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term495 A B x f k) = (term517 A B f k x).
Proof. exact (fun_ext (fun y : B => @lem4620372 A B y f k x)). Qed.
Lemma lem4620374 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4620375 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term497 A B x f k) = (term518 A B f k x).
Proof. exact (MK_COMB (@lem4620374 B) (@lem4620373 A B f k x)). Qed.
Lemma lem4620377 {A : Type'} (P : A -> Prop) (a : A) : (term20 A a P) = (P a).
Proof. exact (EQ_MP (@lem4617700 A P a) (@lem4617699 A P a)). Qed.
Lemma lem4620378 {B : Type'} (P : B -> Prop) (a : B) : (term20 B a P) = (P a).
Proof. exact (@lem4620377 B P a). Qed.
Lemma lem4620379 {A B : Type'} (k : A -> B) (f : A -> B) (x : A) : (term519 A B f k x) = (term520 A B k f x).
Proof. exact (@lem4620378 B (term521 A B f k x) (f x)). Qed.
Lemma lem4620380 {A B : Type'} (y : B) (f : A -> B) (k : A -> B) (x : A) : (term522 A B f k x y) = (term2 A B f k x).
Proof. exact (eq_refl (term522 A B f k x y)). Qed.
Lemma lem4620381 {A B : Type'} (y : B) (f : A -> B) (x : A) : (term303 A B y f x) = (term303 A B y f x).
Proof. exact (eq_refl (term303 A B y f x)). Qed.
Lemma lem4620382 {A B : Type'} (y : B) (f : A -> B) (k : A -> B) (x : A) : (term523 A B f k x y) = (term511 A B y f k x).
Proof. exact (MK_COMB (@lem4620381 A B y f x) (@lem4620380 A B y f k x)). Qed.
Lemma lem4620383 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term524 A B f k x) = (term517 A B f k x).
Proof. exact (fun_ext (fun y : B => @lem4620382 A B y f k x)). Qed.
Lemma lem4620384 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4620385 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term519 A B f k x) = (term518 A B f k x).
Proof. exact (MK_COMB (@lem4620384 B) (@lem4620383 A B f k x)). Qed.
Lemma lem4620386 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4620387 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term525 A B f k x) = (term526 A B f k x).
Proof. exact (MK_COMB (@lem4620386) (@lem4620385 A B f k x)). Qed.
Lemma lem4620388 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term520 A B k f x) = (term2 A B f k x).
Proof. exact (eq_refl (term520 A B k f x)). Qed.
Lemma lem4620389 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : ((term519 A B f k x) = (term520 A B k f x)) = ((term518 A B f k x) = (term2 A B f k x)).
Proof. exact (MK_COMB (@lem4620387 A B f k x) (@lem4620388 A B f k x)). Qed.
Lemma lem4620390 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term518 A B f k x) = (term2 A B f k x).
Proof. exact (EQ_MP (@lem4620389 A B f k x) (@lem4620379 A B k f x)). Qed.
Lemma lem4620393 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term497 A B x f k) = (term2 A B f k x).
Proof. exact (TRANS (@lem4620375 A B f k x) (@lem4620390 A B f k x)). Qed.
Lemma lem4620394 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem4620395 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term499 A B x f k) = (term527 A B f k x).
Proof. exact (MK_COMB (@lem4620394 B) (@lem4620393 A B f k x)). Qed.
Lemma lem4620401 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = (term3 t1 t2 t3).
Proof. exact (EQ_MP (@lem4617715 t1 t2 t3) (@lem4617714 t1 t2 t3)). Qed.
Lemma lem4620402 {A B : Type'} (x : A) (y : B) (f : A -> B) (k : A -> B) (x' : A) : (term490 A B x y f k x') = (term505 A B x y f k x').
Proof. exact (@lem4620401 (x = x') (y = (f x')) (term2 A B f k x')). Qed.
Lemma lem4620413 {A B : Type'} (x : A) (y : B) (f : A -> B) (k : A -> B) : (term492 A B x y f k) = (term506 A B x y f k).
Proof. exact (fun_ext (fun x' : A => @lem4620402 A B x y f k x')). Qed.
Lemma lem4620414 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4620415 {A B : Type'} (x : A) (y : B) (f : A -> B) (k : A -> B) : (term493 A B x y f k) = (term507 A B x y f k).
Proof. exact (MK_COMB (@lem4620414 A) (@lem4620413 A B x y f k)). Qed.
Lemma lem4620419 {A : Type'} (P : A -> Prop) (a : A) : (term24 A a P) = (P a).
Proof. exact (EQ_MP (@lem4617706 A P a) (@lem4617705 A P a)). Qed.
Lemma lem4620420 {A : Type'} (P : A -> Prop) (a : A) : (term24 A a P) = (P a).
Proof. exact (@lem4620419 A P a). Qed.
Lemma lem4620421 {A B : Type'} (y : B) (f : A -> B) (k : A -> B) (x : A) : (term508 A B x y f k) = (term509 A B y f k x).
Proof. exact (@lem4620420 A (term510 A B y f k) x). Qed.
Lemma lem4620422 {A B : Type'} (y : B) (f : A -> B) (k : A -> B) (x' : A) : (term509 A B y f k x') = (term511 A B y f k x').
Proof. exact (eq_refl (term509 A B y f k x')). Qed.
Lemma lem4620423 {A : Type'} (x : A) (x' : A) : (term512 A x x') = (term512 A x x').
Proof. exact (eq_refl (term512 A x x')). Qed.
Lemma lem4620424 {A B : Type'} (x : A) (y : B) (f : A -> B) (k : A -> B) (x' : A) : (term513 A B x y f k x') = (term505 A B x y f k x').
Proof. exact (MK_COMB (@lem4620423 A x x') (@lem4620422 A B y f k x')). Qed.
Lemma lem4620425 {A B : Type'} (x : A) (y : B) (f : A -> B) (k : A -> B) : (term514 A B x y f k) = (term506 A B x y f k).
Proof. exact (fun_ext (fun x' : A => @lem4620424 A B x y f k x')). Qed.
Lemma lem4620426 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4620427 {A B : Type'} (x : A) (y : B) (f : A -> B) (k : A -> B) : (term508 A B x y f k) = (term507 A B x y f k).
Proof. exact (MK_COMB (@lem4620426 A) (@lem4620425 A B x y f k)). Qed.
Lemma lem4620428 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4620429 {A B : Type'} (x : A) (y : B) (f : A -> B) (k : A -> B) : (term515 A B x y f k) = (term516 A B x y f k).
Proof. exact (MK_COMB (@lem4620428) (@lem4620427 A B x y f k)). Qed.
Lemma lem4620430 {A B : Type'} (y : B) (f : A -> B) (k : A -> B) (x : A) : (term509 A B y f k x) = (term511 A B y f k x).
Proof. exact (eq_refl (term509 A B y f k x)). Qed.
Lemma lem4620431 {A B : Type'} (y : B) (f : A -> B) (k : A -> B) (x : A) : ((term508 A B x y f k) = (term509 A B y f k x)) = ((term507 A B x y f k) = (term511 A B y f k x)).
Proof. exact (MK_COMB (@lem4620429 A B x y f k) (@lem4620430 A B y f k x)). Qed.
Lemma lem4620432 {A B : Type'} (y : B) (f : A -> B) (k : A -> B) (x : A) : (term507 A B x y f k) = (term511 A B y f k x).
Proof. exact (EQ_MP (@lem4620431 A B y f k x) (@lem4620421 A B y f k x)). Qed.
Lemma lem4620439 {A B : Type'} (y : B) (f : A -> B) (k : A -> B) (x : A) : (term493 A B x y f k) = (term511 A B y f k x).
Proof. exact (TRANS (@lem4620415 A B x y f k) (@lem4620432 A B y f k x)). Qed.
Lemma lem4620440 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term495 A B x f k) = (term517 A B f k x).
Proof. exact (fun_ext (fun y : B => @lem4620439 A B y f k x)). Qed.
Lemma lem4620441 {B : Type'} : (@ε B) = (@ε B).
Proof. exact (eq_refl (@ε B)). Qed.
Lemma lem4620442 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term501 A B x f k) = (term528 A B f k x).
Proof. exact (MK_COMB (@lem4620441 B) (@lem4620440 A B f k x)). Qed.
Lemma lem4620443 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term503 A B x f k) = (term529 A B f k x).
Proof. exact (MK_COMB (@lem4620395 A B f k x) (@lem4620442 A B f k x)). Qed.
Lemma lem4620444 {A B : Type'} (k : A -> B) (x : A) : (k x) = (k x).
Proof. exact (eq_refl (k x)). Qed.
Lemma lem4620445 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (term504 A B f k x) = (term530 A B f k x).
Proof. exact (MK_COMB (@lem4620443 A B f k x) (@lem4620444 A B k x)). Qed.
Lemma lem4620446 {A B : Type'} (f : A -> B) (x : A) : (term477 A B f x) = (term477 A B f x).
Proof. exact (eq_refl (term477 A B f x)). Qed.
Lemma lem4620447 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : ((f x) = (term504 A B f k x)) = ((f x) = (term530 A B f k x)).
Proof. exact (MK_COMB (@lem4620446 A B f x) (@lem4620445 A B f k x)). Qed.
Lemma lem4620450 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : ((f x) = (term530 A B f k x)) = ((f x) = (term504 A B f k x)).
Proof. exact (SYM (@lem4620447 A B f k x)). Qed.
Lemma lem4620462 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : (f x) = (k x).
Proof. exact (h1). Qed.
Lemma lem4620463 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4620464 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : (term477 A B f x) = (term477 A B k x).
Proof. exact (MK_COMB (@lem4620463 B) (@lem4620462 A B f k x h1)). Qed.
Lemma lem4620468 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : (f x) = (k x).
Proof. exact (h1). Qed.
Lemma lem4620469 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4620470 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : (term477 A B f x) = (term477 A B k x).
Proof. exact (MK_COMB (@lem4620469 B) (@lem4620468 A B f k x h1)). Qed.
Lemma lem4620471 {A B : Type'} (k : A -> B) (x : A) : (k x) = (k x).
Proof. exact (eq_refl (k x)). Qed.
Lemma lem4620472 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : ((f x) = (k x)) = ((k x) = (k x)).
Proof. exact (MK_COMB (@lem4620470 A B f k x h1) (@lem4620471 A B k x)). Qed.
Lemma lem4620474 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4620475 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem4620474 B x). Qed.
Lemma lem4620476 {A B : Type'} (k : A -> B) (x : A) : ((k x) = (k x)) = True.
Proof. exact (@lem4620475 B (k x)). Qed.
Lemma lem4620477 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : ((f x) = (k x)) = True.
Proof. exact (TRANS (@lem4620472 A B f k x h1) (@lem4620476 A B k x)). Qed.
Lemma lem4620478 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4620479 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : (term2 A B f k x) = (~ True).
Proof. exact (MK_COMB (@lem4620478) (@lem4620477 A B f k x h1)). Qed.
Lemma lem4620481 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem4620482 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : (term2 A B f k x) = False.
Proof. exact (TRANS (@lem4620479 A B f k x h1) (@lem4620481)). Qed.
Lemma lem4620483 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem4620484 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : (term527 A B f k x) = (@COND B False).
Proof. exact (MK_COMB (@lem4620483 B) (@lem4620482 A B f k x h1)). Qed.
Lemma lem4620490 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : (f x) = (k x).
Proof. exact (h1). Qed.
Lemma lem4620491 {B : Type'} (y : B) : (@eq B y) = (@eq B y).
Proof. exact (eq_refl (@eq B y)). Qed.
Lemma lem4620492 {A B : Type'} (y : B) (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : (y = (f x)) = (y = (k x)).
Proof. exact (MK_COMB (@lem4620491 B y) (@lem4620490 A B f k x h1)). Qed.
Lemma lem4620495 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4620496 {A B : Type'} (y : B) (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : (term303 A B y f x) = (term303 A B y k x).
Proof. exact (MK_COMB (@lem4620495) (@lem4620492 A B y f k x h1)). Qed.
Lemma lem4620500 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : (f x) = (k x).
Proof. exact (h1). Qed.
Lemma lem4620501 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4620502 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : (term477 A B f x) = (term477 A B k x).
Proof. exact (MK_COMB (@lem4620501 B) (@lem4620500 A B f k x h1)). Qed.
Lemma lem4620503 {A B : Type'} (k : A -> B) (x : A) : (k x) = (k x).
Proof. exact (eq_refl (k x)). Qed.
Lemma lem4620504 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : ((f x) = (k x)) = ((k x) = (k x)).
Proof. exact (MK_COMB (@lem4620502 A B f k x h1) (@lem4620503 A B k x)). Qed.
Lemma lem4620506 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4620507 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem4620506 B x). Qed.
Lemma lem4620508 {A B : Type'} (k : A -> B) (x : A) : ((k x) = (k x)) = True.
Proof. exact (@lem4620507 B (k x)). Qed.
Lemma lem4620509 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : ((f x) = (k x)) = True.
Proof. exact (TRANS (@lem4620504 A B f k x h1) (@lem4620508 A B k x)). Qed.
Lemma lem4620510 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4620511 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : (term2 A B f k x) = (~ True).
Proof. exact (MK_COMB (@lem4620510) (@lem4620509 A B f k x h1)). Qed.
Lemma lem4620513 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem4620514 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : (term2 A B f k x) = False.
Proof. exact (TRANS (@lem4620511 A B f k x h1) (@lem4620513)). Qed.
Lemma lem4620515 {A B : Type'} (y : B) (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : (term511 A B y f k x) = (term531 A B y k x).
Proof. exact (MK_COMB (@lem4620496 A B y f k x h1) (@lem4620514 A B f k x h1)). Qed.
Lemma lem4620517 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem4620518 {A B : Type'} (y : B) (k : A -> B) (x : A) : (term531 A B y k x) = False.
Proof. exact (@lem4620517 (y = (k x))). Qed.
Lemma lem4620519 {A B : Type'} (y : B) (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : (term511 A B y f k x) = False.
Proof. exact (TRANS (@lem4620515 A B y f k x h1) (@lem4620518 A B y k x)). Qed.
Lemma lem4620520 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : (term517 A B f k x) = (term532 B).
Proof. exact (fun_ext (fun y : B => @lem4620519 A B y f k x h1)). Qed.
Lemma lem4620521 {B : Type'} : (@ε B) = (@ε B).
Proof. exact (eq_refl (@ε B)). Qed.
Lemma lem4620522 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : (term528 A B f k x) = (term533 B).
Proof. exact (MK_COMB (@lem4620521 B) (@lem4620520 A B f k x h1)). Qed.
Lemma lem4620523 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : (term529 A B f k x) = (term534 B).
Proof. exact (MK_COMB (@lem4620484 A B f k x h1) (@lem4620522 A B f k x h1)). Qed.
Lemma lem4620524 {A B : Type'} (k : A -> B) (x : A) : (k x) = (k x).
Proof. exact (eq_refl (k x)). Qed.
Lemma lem4620525 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : (term530 A B f k x) = (term535 A B k x).
Proof. exact (MK_COMB (@lem4620523 A B f k x h1) (@lem4620524 A B k x)). Qed.
Lemma lem4620527 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4620528 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem4620527 B t1 t2). Qed.
Lemma lem4620529 {A B : Type'} (k : A -> B) (x : A) : (term535 A B k x) = (k x).
Proof. exact (@lem4620528 B (term533 B) (k x)). Qed.
Lemma lem4620530 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : (term530 A B f k x) = (k x).
Proof. exact (TRANS (@lem4620525 A B f k x h1) (@lem4620529 A B k x)). Qed.
Lemma lem4620531 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : ((f x) = (term530 A B f k x)) = ((k x) = (k x)).
Proof. exact (MK_COMB (@lem4620464 A B f k x h1) (@lem4620530 A B f k x h1)). Qed.
Lemma lem4620533 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4620534 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem4620533 B x). Qed.
Lemma lem4620535 {A B : Type'} (k : A -> B) (x : A) : ((k x) = (k x)) = True.
Proof. exact (@lem4620534 B (k x)). Qed.
Lemma lem4620536 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : ((f x) = (term530 A B f k x)) = True.
Proof. exact (TRANS (@lem4620531 A B f k x h1) (@lem4620535 A B k x)). Qed.
Lemma lem4620537 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : True = ((f x) = (term530 A B f k x)).
Proof. exact (SYM (@lem4620536 A B f k x h1)). Qed.
Lemma lem4620538 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : (f x) = (k x)) : (f x) = (term530 A B f k x).
Proof. exact (EQ_MP (@lem4620537 A B f k x h1) (@lem0)). Qed.
Lemma lem4620547 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : term536 A B f k x.
Proof. exact (@lem82 ((f x) = (k x))). Qed.
Lemma lem4620563 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : ((f x) = (k x)) = False.
Proof. exact (@lem4620547 A B f k x (@lem4617677 A B f k x h1)). Qed.
Lemma lem4620564 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4620565 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : (term2 A B f k x) = (~ False).
Proof. exact (MK_COMB (@lem4620564) (@lem4620563 A B f k x h1)). Qed.
Lemma lem4620567 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4620568 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : (term2 A B f k x) = True.
Proof. exact (TRANS (@lem4620565 A B f k x h1) (@lem4620567)). Qed.
Lemma lem4620569 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem4620570 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : (term527 A B f k x) = (@COND B True).
Proof. exact (MK_COMB (@lem4620569 B) (@lem4620568 A B f k x h1)). Qed.
Lemma lem4620576 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : ((f x) = (k x)) = False.
Proof. exact (@lem4620547 A B f k x (@lem4617677 A B f k x h1)). Qed.
Lemma lem4620577 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4620578 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : (term2 A B f k x) = (~ False).
Proof. exact (MK_COMB (@lem4620577) (@lem4620576 A B f k x h1)). Qed.
Lemma lem4620580 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4620581 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : (term2 A B f k x) = True.
Proof. exact (TRANS (@lem4620578 A B f k x h1) (@lem4620580)). Qed.
Lemma lem4620582 {A B : Type'} (y : B) (f : A -> B) (x : A) : (term303 A B y f x) = (term303 A B y f x).
Proof. exact (eq_refl (term303 A B y f x)). Qed.
Lemma lem4620583 {A B : Type'} (y : B) (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : (term511 A B y f k x) = (term537 A B y f x).
Proof. exact (MK_COMB (@lem4620582 A B y f x) (@lem4620581 A B f k x h1)). Qed.
Lemma lem4620585 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4620586 {A B : Type'} (y : B) (f : A -> B) (x : A) : (term537 A B y f x) = (y = (f x)).
Proof. exact (@lem4620585 (y = (f x))). Qed.
Lemma lem4620589 {A B : Type'} (y : B) (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : (term511 A B y f k x) = (y = (f x)).
Proof. exact (TRANS (@lem4620583 A B y f k x h1) (@lem4620586 A B y f x)). Qed.
Lemma lem4620590 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : (term517 A B f k x) = (term538 A B f x).
Proof. exact (fun_ext (fun y : B => @lem4620589 A B y f k x h1)). Qed.
Lemma lem4620591 {B : Type'} : (@ε B) = (@ε B).
Proof. exact (eq_refl (@ε B)). Qed.
Lemma lem4620592 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : (term528 A B f k x) = (term539 A B f x).
Proof. exact (MK_COMB (@lem4620591 B) (@lem4620590 A B f k x h1)). Qed.
Lemma lem4620594 {A : Type'} (x : A) : (term540 A x) = x.
Proof. exact (EQ_MP (@lem9524 A x) (@lem9523 A x)). Qed.
Lemma lem4620595 {B : Type'} (x : B) : (term540 B x) = x.
Proof. exact (@lem4620594 B x). Qed.
Lemma lem4620596 {A B : Type'} (f : A -> B) (x : A) : (term539 A B f x) = (f x).
Proof. exact (@lem4620595 B (f x)). Qed.
Lemma lem4620597 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : (term528 A B f k x) = (f x).
Proof. exact (TRANS (@lem4620592 A B f k x h1) (@lem4620596 A B f x)). Qed.
Lemma lem4620598 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : (term529 A B f k x) = (term541 A B f x).
Proof. exact (MK_COMB (@lem4620570 A B f k x h1) (@lem4620597 A B f k x h1)). Qed.
Lemma lem4620599 {A B : Type'} (k : A -> B) (x : A) : (k x) = (k x).
Proof. exact (eq_refl (k x)). Qed.
Lemma lem4620600 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : (term530 A B f k x) = (term542 A B f k x).
Proof. exact (MK_COMB (@lem4620598 A B f k x h1) (@lem4620599 A B k x)). Qed.
Lemma lem4620602 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4620603 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem4620602 B t2 t1). Qed.
Lemma lem4620604 {A B : Type'} (k : A -> B) (f : A -> B) (x : A) : (term542 A B f k x) = (f x).
Proof. exact (@lem4620603 B (k x) (f x)). Qed.
Lemma lem4620605 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : (term530 A B f k x) = (f x).
Proof. exact (TRANS (@lem4620600 A B f k x h1) (@lem4620604 A B k f x)). Qed.
Lemma lem4620606 {A B : Type'} (f : A -> B) (x : A) : (term477 A B f x) = (term477 A B f x).
Proof. exact (eq_refl (term477 A B f x)). Qed.
Lemma lem4620607 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : ((f x) = (term530 A B f k x)) = ((f x) = (f x)).
Proof. exact (MK_COMB (@lem4620606 A B f x) (@lem4620605 A B f k x h1)). Qed.
Lemma lem4620609 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4620610 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem4620609 B x). Qed.
Lemma lem4620611 {A B : Type'} (f : A -> B) (x : A) : ((f x) = (f x)) = True.
Proof. exact (@lem4620610 B (f x)). Qed.
Lemma lem4620612 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : ((f x) = (term530 A B f k x)) = True.
Proof. exact (TRANS (@lem4620607 A B f k x h1) (@lem4620611 A B f x)). Qed.
Lemma lem4620613 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : True = ((f x) = (term530 A B f k x)).
Proof. exact (SYM (@lem4620612 A B f k x h1)). Qed.
Lemma lem4620614 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) (h1 : term2 A B f k x) : (f x) = (term530 A B f k x).
Proof. exact (EQ_MP (@lem4620613 A B f k x h1) (@lem0)). Qed.
Lemma lem4620615 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (f x) = (term530 A B f k x).
Proof. exact (or_elim (@lem4617675 A B f k x) (fun h0 : (f x) = (k x) => @lem4620538 A B f k x h0) (fun h0 : term2 A B f k x => @lem4620614 A B f k x h0)). Qed.
Lemma lem4620616 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (f x) = (term504 A B f k x).
Proof. exact (EQ_MP (@lem4620450 A B f k x) (@lem4620615 A B f k x)). Qed.
Lemma lem4620617 {A B : Type'} (f : A -> B) (k : A -> B) (x : A) : (f x) = (term473 A B f k x).
Proof. exact (EQ_MP (@lem4620322 A B f k x) (@lem4620616 A B f k x)). Qed.
Lemma lem4620622 {A B : Type'} (f : A -> B) (k : A -> B) : term480 A B f k.
Proof. exact (fun x : A => @lem4620617 A B f k x). Qed.
Lemma lem4620623 {A B : Type'} (f : A -> B) (k : A -> B) : f = (term469 A B f k).
Proof. exact (EQ_MP (@lem4620146 A B f k) (@lem4620622 A B f k)). Qed.
Lemma lem4620625 {A B : Type'} (k : A -> B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term177 A B f k s) (h4 : term178 A B f s t) : term543 A B f k s t.
Proof. exact (conj (@lem4620623 A B f k) (@lem4620084 A B k f s t h1 h2 h3 h4)). Qed.
Lemma lem4620626 {A B : Type'} (k : A -> B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term177 A B f k s) (h4 : term178 A B f s t) : term214 A B f k s t.
Proof. exact (ex_intro (term213 A B f k s t) (term218 A B f k) (@lem4620625 A B k f s t h1 h2 h3 h4)). Qed.
Lemma lem4620627 {A B : Type'} (k : A -> B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term177 A B f k s) (h4 : term178 A B f s t) : term151 A B f k s t.
Proof. exact (EQ_MP (@lem4618323 A B f k s t) (@lem4620626 A B k f s t h1 h2 h3 h4)). Qed.
Lemma lem4620628 {A B : Type'} (t : B -> Prop) (f : A -> B) (k : A -> B) (s : A -> Prop) (h1 : term133 A B t f k s) : term177 A B f k s.
Proof. exact (proj2 (@lem4618252 A B t f k s h1)). Qed.
Lemma lem4620629 {A B : Type'} (t : B -> Prop) (f : A -> B) (k : A -> B) (s : A -> Prop) (h1 : term133 A B t f k s) : term178 A B f s t.
Proof. exact (proj1 (@lem4618252 A B t f k s h1)). Qed.
Lemma lem4620630 {A B : Type'} (k : A -> B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term177 A B f k s) (h4 : term178 A B f s t) : (term177 A B f k s) = (term151 A B f k s t).
Proof. exact (prop_ext (fun h5 : term177 A B f k s => @lem4620627 A B k f s t h1 h2 h3 h4) (fun h5 : term151 A B f k s t => @lem4618253 A B f k s h3)). Qed.
Lemma lem4620631 {A B : Type'} (k : A -> B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term177 A B f k s) (h4 : term178 A B f s t) : term151 A B f k s t.
Proof. exact (EQ_MP (@lem4620630 A B k f s t h1 h2 h3 h4) (@lem4618253 A B f k s h3)). Qed.
Lemma lem4620632 {A B : Type'} (k : A -> B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term177 A B f k s) (h4 : term178 A B f s t) : (term178 A B f s t) = (term151 A B f k s t).
Proof. exact (prop_ext (fun h5 : term178 A B f s t => @lem4620631 A B k f s t h1 h2 h3 h4) (fun h5 : term151 A B f k s t => @lem4618254 A B f s t h4)). Qed.
Lemma lem4620633 {A B : Type'} (k : A -> B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term177 A B f k s) (h4 : term178 A B f s t) : term151 A B f k s t.
Proof. exact (EQ_MP (@lem4620632 A B k f s t h1 h2 h3 h4) (@lem4618254 A B f s t h4)). Qed.
Lemma lem4620634 {A B : Type'} (k : A -> B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term133 A B t f k s) (h4 : term178 A B f s t) : (term177 A B f k s) = (term151 A B f k s t).
Proof. exact (prop_ext (fun h5 : term177 A B f k s => @lem4620633 A B k f s t h1 h2 h5 h4) (fun h5 : term151 A B f k s t => @lem4620628 A B t f k s h3)). Qed.
Lemma lem4620635 {A B : Type'} (k : A -> B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term133 A B t f k s) (h4 : term178 A B f s t) : term151 A B f k s t.
Proof. exact (EQ_MP (@lem4620634 A B k f s t h1 h2 h3 h4) (@lem4620628 A B t f k s h3)). Qed.
Lemma lem4620636 {A B : Type'} (t : B -> Prop) (f : A -> B) (k : A -> B) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term133 A B t f k s) : (term178 A B f s t) = (term151 A B f k s t).
Proof. exact (prop_ext (fun h4 : term178 A B f s t => @lem4620635 A B k f s t h1 h2 h3 h4) (fun h4 : term151 A B f k s t => @lem4620629 A B t f k s h3)). Qed.
Lemma lem4620637 {A B : Type'} (t : B -> Prop) (f : A -> B) (k : A -> B) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term133 A B t f k s) : term151 A B f k s t.
Proof. exact (EQ_MP (@lem4620636 A B t f k s h1 h2 h3) (@lem4620629 A B t f k s h3)). Qed.
Lemma lem4620638 {A B : Type'} (f : A -> B) (k : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : term174 A B f k s t.
Proof. exact (fun h0 : term133 A B t f k s => @lem4620637 A B t f k s h1 h2 h0). Qed.
Lemma lem4620643 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : term176 A B k s t.
Proof. exact (fun f : A -> B => @lem4620638 A B f k s t h1 h2). Qed.
Lemma lem4620644 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : term123 A B k s t.
Proof. exact (EQ_MP (@lem4618251 A B k s t) (@lem4620643 A B k s t h1 h2)). Qed.
Lemma lem4620645 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : term119 A B k s t.
Proof. exact (EQ_MP (@lem4618163 A B k s t) (@lem4620644 A B k s t h1 h2)). Qed.
Lemma lem4620646 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : term120 A B k s t.
Proof. exact (EQ_MP (@lem4618158 A B k s t h1 h2) (@lem4620645 A B k s t h1 h2)). Qed.
Lemma lem4620647 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : term544 A B t k s.
Proof. exact (ex_intro (term545 A B t k s) (term124 A B k s t) (@lem4620646 A B k s t h1 h2)). Qed.
Lemma lem4620648 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : term546 A B t k s.
Proof. exact (@lem4617954 A B t k s (@lem4620647 A B k s t h1 h2)). Qed.
Lemma lem4620649 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term89 A B s t) : @FINITE B t.
Proof. exact (proj2 (@lem4617948 A B s t h1)). Qed.
Lemma lem4620650 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term89 A B s t) : @FINITE A s.
Proof. exact (proj1 (@lem4617948 A B s t h1)). Qed.
Lemma lem4620651 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : (@FINITE B t) = (term546 A B t k s).
Proof. exact (prop_ext (fun h3 : @FINITE B t => @lem4620648 A B k s t h1 h2) (fun h3 : term546 A B t k s => @lem4617949 B t h2)). Qed.
Lemma lem4620652 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : term546 A B t k s.
Proof. exact (EQ_MP (@lem4620651 A B k s t h1 h2) (@lem4617949 B t h2)). Qed.
Lemma lem4620653 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : (@FINITE A s) = (term546 A B t k s).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem4620652 A B k s t h1 h2) (fun h3 : term546 A B t k s => @lem4617950 A s h1)). Qed.
Lemma lem4620654 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : term546 A B t k s.
Proof. exact (EQ_MP (@lem4620653 A B k s t h1 h2) (@lem4617950 A s h1)). Qed.
Lemma lem4620655 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term89 A B s t) : (@FINITE B t) = (term546 A B t k s).
Proof. exact (prop_ext (fun h3 : @FINITE B t => @lem4620654 A B k s t h1 h3) (fun h3 : term546 A B t k s => @lem4620649 A B s t h2)). Qed.
Lemma lem4620656 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term89 A B s t) : term546 A B t k s.
Proof. exact (EQ_MP (@lem4620655 A B k s t h1 h2) (@lem4620649 A B s t h2)). Qed.
Lemma lem4620657 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term89 A B s t) : (@FINITE A s) = (term546 A B t k s).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem4620656 A B k s t h2 h1) (fun h2 : term546 A B t k s => @lem4620650 A B s t h1)). Qed.
Lemma lem4620658 {A B : Type'} (k : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term89 A B s t) : term546 A B t k s.
Proof. exact (EQ_MP (@lem4620657 A B k s t h1) (@lem4620650 A B s t h1)). Qed.
Lemma lem4620659 {A B : Type'} (t : B -> Prop) (k : A -> B) (s : A -> Prop) : term547 A B t k s.
Proof. exact (fun h0 : term89 A B s t => @lem4620658 A B k s t h0). Qed.
Lemma lem4620664 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term548 A B t s.
Proof. exact (fun k : A -> B => @lem4620659 A B t k s). Qed.
Lemma lem4620669 {A B : Type'} (s : A -> Prop) : term549 A B s.
Proof. exact (fun t : B -> Prop => @lem4620664 A B t s). Qed.
Lemma lem4620674 {A B : Type'} : term550 A B.
Proof. exact (fun s : A -> Prop => @lem4620669 A B s). Qed.
