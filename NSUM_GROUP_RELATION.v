Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_GROUP_RELATION_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FORALL_IN_IMAGE_spec.
Require Import NSUM_EQ_spec.
Require Import NSUM_GROUP_spec.
Require Import SUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm129_spec.
Require Import thm137_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1842_spec.
Require Import thm18897_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18940_spec.
Require Import thm18941_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19490_spec.
Require Import thm19732_spec.
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
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm51_spec.
Require Import thm7_spec.
Lemma lem6994743 {_127166 : Type'} (h1 : term0 _127166) : term0 _127166.
Proof. exact (h1). Qed.
Lemma lem6994744 {_127166 : Type'} (f : _127166 -> nat) (h1 : term0 _127166) : term1 _127166 f.
Proof. exact (@lem6994743 _127166 h1 f). Qed.
Lemma lem6994745 {_127166 : Type'} (f : _127166 -> nat) : (term1 _127166 f) = (term2 _127166 f).
Proof. exact (eq_refl (term1 _127166 f)). Qed.
Lemma lem6994746 {_127166 : Type'} (f : _127166 -> nat) (h1 : term0 _127166) : term2 _127166 f.
Proof. exact (EQ_MP (@lem6994745 _127166 f) (@lem6994744 _127166 f h1)). Qed.
Lemma lem6994747 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) (h1 : term0 _127166) : term3 _127166 f g.
Proof. exact (@lem6994746 _127166 f h1 g). Qed.
Lemma lem6994748 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term3 _127166 f g) = (term4 _127166 f g).
Proof. exact (eq_refl (term3 _127166 f g)). Qed.
Lemma lem6994749 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) (h1 : term0 _127166) : term4 _127166 f g.
Proof. exact (EQ_MP (@lem6994748 _127166 f g) (@lem6994747 _127166 f g h1)). Qed.
Lemma lem6994750 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) (s : _127166 -> Prop) (h1 : term0 _127166) : term5 _127166 f g s.
Proof. exact (@lem6994749 _127166 f g h1 s). Qed.
Lemma lem6994751 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term5 _127166 f g s) = (term6 _127166 f s g).
Proof. exact (eq_refl (term5 _127166 f g s)). Qed.
Lemma lem6994752 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) (h1 : term0 _127166) : term6 _127166 f s g.
Proof. exact (EQ_MP (@lem6994751 _127166 f s g) (@lem6994750 _127166 f g s h1)). Qed.
Lemma lem6994753 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (h1 : term7 _127166 s f g) : term7 _127166 s f g.
Proof. exact (h1). Qed.
Lemma lem6994754 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (h1 : term7 _127166 s f g) (h2 : term0 _127166) : (@nsum _127166 s f) = (@nsum _127166 s g).
Proof. exact (@lem6994752 _127166 f s g h2 (@lem6994753 _127166 s f g h1)). Qed.
Lemma lem6994755 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (h1 : term7 _127166 s f g) : term8 _127166 f s g.
Proof. exact (fun h0 : term0 _127166 => @lem6994754 _127166 s f g h1 h0). Qed.
Lemma lem6994756 {_127166 : Type'} (h1 : term0 _127166) : term0 _127166.
Proof. exact (h1). Qed.
Lemma lem6994757 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (h1 : term7 _127166 s f g) (h2 : term0 _127166) : (@nsum _127166 s f) = (@nsum _127166 s g).
Proof. exact (@lem6994755 _127166 s f g h1 (@lem6994756 _127166 h2)). Qed.
Lemma lem6994758 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) (h1 : term0 _127166) : term6 _127166 f s g.
Proof. exact (fun h0 : term7 _127166 s f g => @lem6994757 _127166 s f g h0 h1). Qed.
Lemma lem6994759 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (h1 : term0 _127166) : term9 _127166 f s.
Proof. exact (fun g : _127166 -> nat => @lem6994758 _127166 f s g h1). Qed.
Lemma lem6994760 {_127166 : Type'} (f : _127166 -> nat) (h1 : term0 _127166) : term10 _127166 f.
Proof. exact (fun s : _127166 -> Prop => @lem6994759 _127166 f s h1). Qed.
Lemma lem6994761 {_127166 : Type'} (h1 : term0 _127166) : term11 _127166.
Proof. exact (fun f : _127166 -> nat => @lem6994760 _127166 f h1). Qed.
Lemma lem6994762 {_127166 : Type'} : term12 _127166.
Proof. exact (fun h0 : term0 _127166 => @lem6994761 _127166 h0). Qed.
Lemma lem6994763 {_127166 : Type'} : term11 _127166.
Proof. exact (@lem6994762 _127166 (@lem6938831 _127166)). Qed.
Lemma lem6994764 {_127166 : Type'} (f : _127166 -> nat) : term13 _127166 f.
Proof. exact (@lem6994763 _127166 f). Qed.
Lemma lem6994765 {_127166 : Type'} (f : _127166 -> nat) : (term13 _127166 f) = (term10 _127166 f).
Proof. exact (eq_refl (term13 _127166 f)). Qed.
Lemma lem6994766 {_127166 : Type'} (f : _127166 -> nat) : term10 _127166 f.
Proof. exact (EQ_MP (@lem6994765 _127166 f) (@lem6994764 _127166 f)). Qed.
Lemma lem6994767 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) : term14 _127166 f s.
Proof. exact (@lem6994766 _127166 f s). Qed.
Lemma lem6994768 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) : (term14 _127166 f s) = (term9 _127166 f s).
Proof. exact (eq_refl (term14 _127166 f s)). Qed.
Lemma lem6994769 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) : term9 _127166 f s.
Proof. exact (EQ_MP (@lem6994768 _127166 f s) (@lem6994767 _127166 f s)). Qed.
Lemma lem6994770 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : term15 _127166 f s g.
Proof. exact (@lem6994769 _127166 f s g). Qed.
Lemma lem6994771 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term15 _127166 f s g) = (term6 _127166 f s g).
Proof. exact (eq_refl (term15 _127166 f s g)). Qed.
Lemma lem6994773 (t1 : Prop) : term16 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem6994774 (t1 : Prop) : (term16 t1) = (term17 t1).
Proof. exact (eq_refl (term16 t1)). Qed.
Lemma lem6994775 (t1 : Prop) : term17 t1.
Proof. exact (EQ_MP (@lem6994774 t1) (@lem6994773 t1)). Qed.
Lemma lem6994776 (t1 : Prop) (t2 : Prop) : term18 t1 t2.
Proof. exact (@lem6994775 t1 t2). Qed.
Lemma lem6994777 (t1 : Prop) (t2 : Prop) : (term18 t1 t2) = (term19 t1 t2).
Proof. exact (eq_refl (term18 t1 t2)). Qed.
Lemma lem6994778 (t1 : Prop) (t2 : Prop) : term19 t1 t2.
Proof. exact (EQ_MP (@lem6994777 t1 t2) (@lem6994776 t1 t2)). Qed.
Lemma lem6994779 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term20 t1 t2 t3.
Proof. exact (@lem6994778 t1 t2 t3). Qed.
Lemma lem6994780 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term20 t1 t2 t3) = ((term21 t1 t2 t3) = (term22 t1 t2 t3)).
Proof. exact (eq_refl (term20 t1 t2 t3)). Qed.
Lemma lem6994781 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term21 t1 t2 t3) = (term22 t1 t2 t3).
Proof. exact (EQ_MP (@lem6994780 t1 t2 t3) (@lem6994779 t1 t2 t3)). Qed.
Lemma lem6994782 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term22 t1 t2 t3) = (term21 t1 t2 t3).
Proof. exact (SYM (@lem6994781 t1 t2 t3)). Qed.
Lemma lem6994783 {A B : Type'} : term23 A B.
Proof. exact (@lem6994742 A B). Qed.
Lemma lem6994784 {A B : Type'} (t : B -> Prop) (R : type1413 A B) : term24 A B t R.
Proof. exact (@lem6994783 A B (term25 A B t R)). Qed.
Lemma lem6994785 {A B : Type'} (t : B -> Prop) (R : type1413 A B) : (term24 A B t R) = (term26 A B t R).
Proof. exact (eq_refl (term24 A B t R)). Qed.
Lemma lem6994786 {A B : Type'} (t : B -> Prop) (R : type1413 A B) : term26 A B t R.
Proof. exact (EQ_MP (@lem6994785 A B t R) (@lem6994784 A B t R)). Qed.
Lemma lem6994787 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (g : A -> nat) : term27 A B t R g.
Proof. exact (@lem6994786 A B t R g). Qed.
Lemma lem6994788 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (g : A -> nat) : (term27 A B t R g) = (term28 A B t R g).
Proof. exact (eq_refl (term27 A B t R g)). Qed.
Lemma lem6994789 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (g : A -> nat) : term28 A B t R g.
Proof. exact (EQ_MP (@lem6994788 A B t R g) (@lem6994787 A B t R g)). Qed.
Lemma lem6994790 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (g : A -> nat) (s : A -> Prop) : term29 A B t R g s.
Proof. exact (@lem6994789 A B t R g s). Qed.
Lemma lem6994791 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> nat) : (term29 A B t R g s) = (term30 A B t R s g).
Proof. exact (eq_refl (term29 A B t R g s)). Qed.
Lemma lem6994792 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> nat) : term30 A B t R s g.
Proof. exact (EQ_MP (@lem6994791 A B t R s g) (@lem6994790 A B t R g s)). Qed.
Lemma lem6994793 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (g : A -> nat) (t : B -> Prop) : term31 A B R s g t.
Proof. exact (@lem6994792 A B t R s g t). Qed.
Lemma lem6994794 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> nat) : (term31 A B R s g t) = (term32 A B t R s g).
Proof. exact (eq_refl (term31 A B R s g t)). Qed.
Lemma lem6994795 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> nat) : term32 A B t R s g.
Proof. exact (EQ_MP (@lem6994794 A B t R s g) (@lem6994793 A B R s g t)). Qed.
Lemma lem6994796 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (h1 : term33 A B s t R) : term33 A B s t R.
Proof. exact (h1). Qed.
Lemma lem6994797 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (h1 : term34 A B s t R) : term34 A B s t R.
Proof. exact (h1). Qed.
Lemma lem6994798 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem6994799 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term35 _87967 _87968 P f.
Proof. exact (@lem3386920 _87967 _87968 P f). Qed.
Lemma lem6994800 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : (term35 _87967 _87968 P f) = (term36 _87967 _87968 P f).
Proof. exact (eq_refl (term35 _87967 _87968 P f)). Qed.
Lemma lem6994801 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term36 _87967 _87968 P f.
Proof. exact (EQ_MP (@lem6994800 _87967 _87968 P f) (@lem6994799 _87967 _87968 P f)). Qed.
Lemma lem6994802 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (s : _87968 -> Prop) : term37 _87967 _87968 P f s.
Proof. exact (@lem6994801 _87967 _87968 P f s). Qed.
Lemma lem6994803 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term37 _87967 _87968 P f s) = ((term38 _87967 _87968 f s P) = (term39 _87967 _87968 s P f)).
Proof. exact (eq_refl (term37 _87967 _87968 P f s)). Qed.
Lemma lem6994805 {A : Type'} (s : A -> Prop) : term40 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem6994806 {A : Type'} (s : A -> Prop) : (term40 A s) = (term41 A s).
Proof. exact (eq_refl (term40 A s)). Qed.
Lemma lem6994807 {A : Type'} (s : A -> Prop) : term41 A s.
Proof. exact (EQ_MP (@lem6994806 A s) (@lem6994805 A s)). Qed.
Lemma lem6994808 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term42 A s t.
Proof. exact (@lem6994807 A s t). Qed.
Lemma lem6994809 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term42 A s t) = ((@SUBSET A s t) = (term43 A s t)).
Proof. exact (eq_refl (term42 A s t)). Qed.
Lemma lem6994811 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem6994825 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6994811 A s) (@lem6994798 A s h1)). Qed.
Lemma lem6994826 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6994827 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term44 A s) = (and True).
Proof. exact (MK_COMB (@lem6994826) (@lem6994825 A s h1)). Qed.
Lemma lem6994829 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term43 A s t).
Proof. exact (EQ_MP (@lem6994809 A s t) (@lem6994808 A s t)). Qed.
Lemma lem6994830 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term43 B s t).
Proof. exact (@lem6994829 B s t). Qed.
Lemma lem6994831 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (t : B -> Prop) : (term45 A B R s t) = (term46 A B R s t).
Proof. exact (@lem6994830 B (term47 A B t R s) t). Qed.
Lemma lem6994833 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term38 _87967 _87968 f s P) = (term39 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem6994803 _87967 _87968 s P f) (@lem6994802 _87967 _87968 P f s)). Qed.
Lemma lem6994834 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term48 A B f s P) = (term49 A B s P f).
Proof. exact (@lem6994833 B A s P f). Qed.
Lemma lem6994835 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term50 A B R s t) = (term51 A B s t R).
Proof. exact (@lem6994834 A B s (term52 B t) (term25 A B t R)). Qed.
Lemma lem6994836 {B : Type'} (x : B) (t : B -> Prop) : (term53 B t x) = (@IN B x t).
Proof. exact (eq_refl (term53 B t x)). Qed.
Lemma lem6994837 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term54 A B x t R s) = (term54 A B x t R s).
Proof. exact (eq_refl (term54 A B x t R s)). Qed.
Lemma lem6994838 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (x : B) (t : B -> Prop) : (term55 A B R s t x) = (term56 A B R s x t).
Proof. exact (MK_COMB (@lem6994837 A B x t R s) (@lem6994836 B x t)). Qed.
Lemma lem6994839 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (t : B -> Prop) : (term57 A B R s t) = (term58 A B R s t).
Proof. exact (fun_ext (fun x : B => @lem6994838 A B R s x t)). Qed.
Lemma lem6994840 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6994841 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (t : B -> Prop) : (term50 A B R s t) = (term46 A B R s t).
Proof. exact (MK_COMB (@lem6994840 B) (@lem6994839 A B R s t)). Qed.
Lemma lem6994842 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6994843 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (t : B -> Prop) : (term59 A B R s t) = (term60 A B R s t).
Proof. exact (MK_COMB (@lem6994842) (@lem6994841 A B R s t)). Qed.
Lemma lem6994844 {A B : Type'} (R : type1413 A B) (x : A) (t : B -> Prop) : (term61 A B t R x) = (term62 A B R x t).
Proof. exact (eq_refl (term61 A B t R x)). Qed.
Lemma lem6994845 {A : Type'} (x : A) (s : A -> Prop) : (term63 A x s) = (term63 A x s).
Proof. exact (eq_refl (term63 A x s)). Qed.
Lemma lem6994846 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : A) (t : B -> Prop) : (term64 A B s t R x) = (term65 A B s R x t).
Proof. exact (MK_COMB (@lem6994845 A x s) (@lem6994844 A B R x t)). Qed.
Lemma lem6994847 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term66 A B s t R) = (term67 A B s R t).
Proof. exact (fun_ext (fun x : A => @lem6994846 A B s R x t)). Qed.
Lemma lem6994848 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6994849 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term51 A B s t R) = (term68 A B s R t).
Proof. exact (MK_COMB (@lem6994848 A) (@lem6994847 A B s R t)). Qed.
Lemma lem6994850 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : ((term50 A B R s t) = (term51 A B s t R)) = ((term46 A B R s t) = (term68 A B s R t)).
Proof. exact (MK_COMB (@lem6994843 A B R s t) (@lem6994849 A B s R t)). Qed.
Lemma lem6994851 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term46 A B R s t) = (term68 A B s R t).
Proof. exact (EQ_MP (@lem6994850 A B s R t) (@lem6994835 A B s t R)). Qed.
Lemma lem6994856 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term45 A B R s t) = (term68 A B s R t).
Proof. exact (TRANS (@lem6994831 A B R s t) (@lem6994851 A B s R t)). Qed.
Lemma lem6994860 {A B : Type'} (f : A -> B) (y : A) : (term69 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6994861 {A B : Type'} (f : A -> B) (y : A) : (term69 A B f y) = (f y).
Proof. exact (@lem6994860 A B f y). Qed.
Lemma lem6994862 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term70 A B t R x) = (term71 A B t R x).
Proof. exact (@lem6994861 A B (term25 A B t R) x). Qed.
Lemma lem6994863 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term71 A B t R x) = (term72 A B t R x).
Proof. exact (eq_refl (term71 A B t R x)). Qed.
Lemma lem6994864 {A B : Type'} (t : B -> Prop) (R : type1413 A B) : (term73 A B t R) = (term25 A B t R).
Proof. exact (fun_ext (fun x : A => @lem6994863 A B t R x)). Qed.
Lemma lem6994865 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6994866 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term70 A B t R x) = (term71 A B t R x).
Proof. exact (MK_COMB (@lem6994864 A B t R) (@lem6994865 A x)). Qed.
Lemma lem6994867 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6994868 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term74 A B t R x) = (term75 A B t R x).
Proof. exact (MK_COMB (@lem6994867 B) (@lem6994866 A B t R x)). Qed.
Lemma lem6994869 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term71 A B t R x) = (term72 A B t R x).
Proof. exact (eq_refl (term71 A B t R x)). Qed.
Lemma lem6994870 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : ((term70 A B t R x) = (term71 A B t R x)) = ((term71 A B t R x) = (term72 A B t R x)).
Proof. exact (MK_COMB (@lem6994868 A B t R x) (@lem6994869 A B t R x)). Qed.
Lemma lem6994871 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term71 A B t R x) = (term72 A B t R x).
Proof. exact (EQ_MP (@lem6994870 A B t R x) (@lem6994862 A B t R x)). Qed.
Lemma lem6994874 {B : Type'} : (@IN B) = (@IN B).
Proof. exact (eq_refl (@IN B)). Qed.
Lemma lem6994875 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term76 A B t R x) = (term77 A B t R x).
Proof. exact (MK_COMB (@lem6994874 B) (@lem6994871 A B t R x)). Qed.
Lemma lem6994876 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem6994877 {A B : Type'} (R : type1413 A B) (x : A) (t : B -> Prop) : (term62 A B R x t) = (term78 A B R x t).
Proof. exact (MK_COMB (@lem6994875 A B t R x) (@lem6994876 B t)). Qed.
Lemma lem6994878 {A : Type'} (x : A) (s : A -> Prop) : (term63 A x s) = (term63 A x s).
Proof. exact (eq_refl (term63 A x s)). Qed.
Lemma lem6994879 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : A) (t : B -> Prop) : (term65 A B s R x t) = (term79 A B s R x t).
Proof. exact (MK_COMB (@lem6994878 A x s) (@lem6994877 A B R x t)). Qed.
Lemma lem6994882 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term67 A B s R t) = (term80 A B s R t).
Proof. exact (fun_ext (fun x : A => @lem6994879 A B s R x t)). Qed.
Lemma lem6994883 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6994884 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term68 A B s R t) = (term81 A B s R t).
Proof. exact (MK_COMB (@lem6994883 A) (@lem6994882 A B s R t)). Qed.
Lemma lem6994889 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term45 A B R s t) = (term81 A B s R t).
Proof. exact (TRANS (@lem6994856 A B s R t) (@lem6994884 A B s R t)). Qed.
Lemma lem6994890 {A B : Type'} (R : type1413 A B) (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term82 A B R s t) = (term83 A B s R t).
Proof. exact (MK_COMB (@lem6994827 A s h1) (@lem6994889 A B s R t)). Qed.
Lemma lem6994892 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6994893 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term83 A B s R t) = (term81 A B s R t).
Proof. exact (@lem6994892 (term81 A B s R t)). Qed.
Lemma lem6994902 {A B : Type'} (R : type1413 A B) (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term82 A B R s t) = (term81 A B s R t).
Proof. exact (TRANS (@lem6994890 A B R t s h1) (@lem6994893 A B s R t)). Qed.
Lemma lem6994903 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6994904 {A B : Type'} (R : type1413 A B) (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term84 A B R s t) = (term85 A B s R t).
Proof. exact (MK_COMB (@lem6994903) (@lem6994902 A B R t s h1)). Qed.
Lemma lem6994916 {A B : Type'} (f : A -> B) (y : A) : (term69 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6994917 {A B : Type'} (f : A -> B) (y : A) : (term69 A B f y) = (f y).
Proof. exact (@lem6994916 A B f y). Qed.
Lemma lem6994918 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term70 A B t R x) = (term71 A B t R x).
Proof. exact (@lem6994917 A B (term25 A B t R) x). Qed.
Lemma lem6994919 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term71 A B t R x) = (term72 A B t R x).
Proof. exact (eq_refl (term71 A B t R x)). Qed.
Lemma lem6994920 {A B : Type'} (t : B -> Prop) (R : type1413 A B) : (term73 A B t R) = (term25 A B t R).
Proof. exact (fun_ext (fun x : A => @lem6994919 A B t R x)). Qed.
Lemma lem6994921 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6994922 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term70 A B t R x) = (term71 A B t R x).
Proof. exact (MK_COMB (@lem6994920 A B t R) (@lem6994921 A x)). Qed.
Lemma lem6994923 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6994924 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term74 A B t R x) = (term75 A B t R x).
Proof. exact (MK_COMB (@lem6994923 B) (@lem6994922 A B t R x)). Qed.
Lemma lem6994925 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term71 A B t R x) = (term72 A B t R x).
Proof. exact (eq_refl (term71 A B t R x)). Qed.
Lemma lem6994926 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : ((term70 A B t R x) = (term71 A B t R x)) = ((term71 A B t R x) = (term72 A B t R x)).
Proof. exact (MK_COMB (@lem6994924 A B t R x) (@lem6994925 A B t R x)). Qed.
Lemma lem6994927 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term71 A B t R x) = (term72 A B t R x).
Proof. exact (EQ_MP (@lem6994926 A B t R x) (@lem6994918 A B t R x)). Qed.
Lemma lem6994930 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6994931 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term75 A B t R x) = (term86 A B t R x).
Proof. exact (MK_COMB (@lem6994930 B) (@lem6994927 A B t R x)). Qed.
Lemma lem6994932 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6994933 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : ((term71 A B t R x) = y) = ((term72 A B t R x) = y).
Proof. exact (MK_COMB (@lem6994931 A B t R x) (@lem6994932 B y)). Qed.
Lemma lem6994936 {A : Type'} (x : A) (s : A -> Prop) : (term87 A x s) = (term87 A x s).
Proof. exact (eq_refl (term87 A x s)). Qed.
Lemma lem6994937 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term88 A B s t R x y) = (term89 A B s t R x y).
Proof. exact (MK_COMB (@lem6994936 A x s) (@lem6994933 A B t R x y)). Qed.
Lemma lem6994940 {A : Type'} (GEN_PVAR_296 : A) : (@SETSPEC A GEN_PVAR_296) = (@SETSPEC A GEN_PVAR_296).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_296)). Qed.
Lemma lem6994941 {A B : Type'} (GEN_PVAR_296 : A) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term90 A B GEN_PVAR_296 s t R x y) = (term91 A B GEN_PVAR_296 s t R x y).
Proof. exact (MK_COMB (@lem6994940 A GEN_PVAR_296) (@lem6994937 A B s t R x y)). Qed.
Lemma lem6994942 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6994943 {A B : Type'} (GEN_PVAR_296 : A) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (y : B) (x : A) : (term92 A B GEN_PVAR_296 s t R y x) = (term93 A B GEN_PVAR_296 s t R y x).
Proof. exact (MK_COMB (@lem6994941 A B GEN_PVAR_296 s t R x y) (@lem6994942 A x)). Qed.
Lemma lem6994944 {A B : Type'} (GEN_PVAR_296 : A) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (y : B) : (term94 A B GEN_PVAR_296 s t R y) = (term95 A B GEN_PVAR_296 s t R y).
Proof. exact (fun_ext (fun x : A => @lem6994943 A B GEN_PVAR_296 s t R y x)). Qed.
Lemma lem6994945 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6994946 {A B : Type'} (GEN_PVAR_296 : A) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (y : B) : (term96 A B GEN_PVAR_296 s t R y) = (term97 A B GEN_PVAR_296 s t R y).
Proof. exact (MK_COMB (@lem6994945 A) (@lem6994944 A B GEN_PVAR_296 s t R y)). Qed.
Lemma lem6994951 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (y : B) : (term98 A B s t R y) = (term99 A B s t R y).
Proof. exact (fun_ext (fun GEN_PVAR_296 : A => @lem6994946 A B GEN_PVAR_296 s t R y)). Qed.
Lemma lem6994952 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6994953 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (y : B) : (term100 A B s t R y) = (term101 A B s t R y).
Proof. exact (MK_COMB (@lem6994952 A) (@lem6994951 A B s t R y)). Qed.
Lemma lem6994954 {A : Type'} : (@nsum A) = (@nsum A).
Proof. exact (eq_refl (@nsum A)). Qed.
Lemma lem6994955 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (y : B) : (term102 A B s t R y) = (term103 A B s t R y).
Proof. exact (MK_COMB (@lem6994954 A) (@lem6994953 A B s t R y)). Qed.
Lemma lem6994956 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6994957 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (y : B) (g : A -> nat) : (term104 A B s t R y g) = (term105 A B s t R y g).
Proof. exact (MK_COMB (@lem6994955 A B s t R y) (@lem6994956 A g)). Qed.
Lemma lem6994958 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (g : A -> nat) : (term106 A B s t R g) = (term107 A B s t R g).
Proof. exact (fun_ext (fun y : B => @lem6994957 A B s t R y g)). Qed.
Lemma lem6994959 {B : Type'} (t : B -> Prop) : (@nsum B t) = (@nsum B t).
Proof. exact (eq_refl (@nsum B t)). Qed.
Lemma lem6994960 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (g : A -> nat) : (term108 A B s t R g) = (term109 A B s t R g).
Proof. exact (MK_COMB (@lem6994959 B t) (@lem6994958 A B s t R g)). Qed.
Lemma lem6994961 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6994962 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (g : A -> nat) : (term110 A B s t R g) = (term111 A B s t R g).
Proof. exact (MK_COMB (@lem6994961) (@lem6994960 A B s t R g)). Qed.
Lemma lem6994963 {A : Type'} (s : A -> Prop) (g : A -> nat) : (@nsum A s g) = (@nsum A s g).
Proof. exact (eq_refl (@nsum A s g)). Qed.
Lemma lem6994964 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> nat) : ((term108 A B s t R g) = (@nsum A s g)) = ((term109 A B s t R g) = (@nsum A s g)).
Proof. exact (MK_COMB (@lem6994962 A B s t R g) (@lem6994963 A s g)). Qed.
Lemma lem6994967 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (g : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) : (term32 A B t R s g) = (term112 A B t R s g).
Proof. exact (MK_COMB (@lem6994904 A B R t s h1) (@lem6994964 A B t R s g)). Qed.
Lemma lem6994970 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6994971 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (g : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) : (term113 A B t R s g) = (term114 A B t R s g).
Proof. exact (MK_COMB (@lem6994970) (@lem6994967 A B t R g s h1)). Qed.
Lemma lem6994980 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> nat) : ((term115 A B t s R g) = (@nsum A s g)) = ((term115 A B t s R g) = (@nsum A s g)).
Proof. exact (eq_refl ((term115 A B t s R g) = (@nsum A s g))). Qed.
Lemma lem6994981 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (g : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) : (term116 A B t R s g) = (term117 A B t R s g).
Proof. exact (MK_COMB (@lem6994971 A B t R g s h1) (@lem6994980 A B t R s g)). Qed.
Lemma lem6994984 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (g : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) : (term117 A B t R s g) = (term116 A B t R s g).
Proof. exact (SYM (@lem6994981 A B t R g s h1)). Qed.
Lemma lem6994986 (p : Prop) (q : Prop) (r : Prop) : term118 p q r.
Proof. exact (@lem137 p q r (@lem129 p q r)). Qed.
Lemma lem6994987 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> nat) : term119 A B t R s g.
Proof. exact (@lem6994986 (term81 A B s R t) ((term109 A B s t R g) = (@nsum A s g)) ((term115 A B t s R g) = (@nsum A s g))). Qed.
Lemma lem6994989 (p : Prop) : p = (term120 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6994990 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term81 A B s R t) = (term121 A B s R t).
Proof. exact (@lem6994989 (term81 A B s R t)). Qed.
Lemma lem6994991 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term121 A B s R t) = (term81 A B s R t).
Proof. exact (SYM (@lem6994990 A B s R t)). Qed.
Lemma lem6994992 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term122 A B s R t) : term122 A B s R t.
Proof. exact (h1). Qed.
Lemma lem6995003 {B : Type'} (P : B -> Prop) : term123 B P.
Proof. exact (@lem19732 B P). Qed.
Lemma lem6995004 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : term124 A B t R x.
Proof. exact (@lem6995003 B (term125 A B t R x)). Qed.
Lemma lem6995005 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term126 A B t R x) = (term127 A B t R x).
Proof. exact (eq_refl (term126 A B t R x)). Qed.
Lemma lem6995006 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term128 A B t R x x') = (term129 A B t R x x').
Proof. exact (eq_refl (term128 A B t R x x')). Qed.
Lemma lem6995007 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6995008 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term130 A B t R x x') = (term131 A B t R x x').
Proof. exact (MK_COMB (@lem6995007) (@lem6995006 A B t R x x')). Qed.
Lemma lem6995009 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term132 A B x t R x') = (term133 A B x t R x').
Proof. exact (MK_COMB (@lem6995008 A B t R x' x) (@lem6995005 A B t R x')). Qed.
Lemma lem6995010 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term134 A B t R x) = (term135 A B t R x).
Proof. exact (fun_ext (fun x' : B => @lem6995009 A B x' t R x)). Qed.
Lemma lem6995011 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6995012 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term124 A B t R x) = (term136 A B t R x).
Proof. exact (MK_COMB (@lem6995011 B) (@lem6995010 A B t R x)). Qed.
Lemma lem6995013 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : term136 A B t R x.
Proof. exact (EQ_MP (@lem6995012 A B t R x) (@lem6995004 A B t R x)). Qed.
Lemma lem6995014 {A B : Type'} (t : B -> Prop) (R : type1413 A B) : term137 A B t R.
Proof. exact (fun x : A => @lem6995013 A B t R x). Qed.
Lemma lem6995015 {A B : Type'} (t : B -> Prop) : term138 A B t.
Proof. exact (fun R : type1413 A B => @lem6995014 A B t R). Qed.
Lemma lem6995016 {A B : Type'} : term139 A B.
Proof. exact (fun t : B -> Prop => @lem6995015 A B t). Qed.
Lemma lem6995017 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term140 A B s R t) : term140 A B s R t.
Proof. exact (h1). Qed.
Lemma lem6995018 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term140 A B s R t) : term141 A B s R t.
Proof. exact (@lem6995017 A B s R t h1 (@lem6995016 A B)). Qed.
Lemma lem6995019 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term142 A B s R t.
Proof. exact (fun h0 : term140 A B s R t => @lem6995018 A B s R t h0). Qed.
Lemma lem6995020 {A B : Type'} (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : _93258 = (term143 A B).
Proof. exact (h1). Qed.
Lemma lem6995021 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem6995022 {A B : Type'} (t : B -> Prop) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (_93258 t) = (term144 A B t).
Proof. exact (MK_COMB (@lem6995020 A B _93258 h1) (@lem6995021 B t)). Qed.
Lemma lem6995023 {A B : Type'} (t : B -> Prop) : (term144 A B t) = (term145 A B t).
Proof. exact (eq_refl (term144 A B t)). Qed.
Lemma lem6995024 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) : (term146 A B _93258 t) = (term146 A B _93258 t).
Proof. exact (eq_refl (term146 A B _93258 t)). Qed.
Lemma lem6995025 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) : ((_93258 t) = (term144 A B t)) = ((_93258 t) = (term145 A B t)).
Proof. exact (MK_COMB (@lem6995024 A B _93258 t) (@lem6995023 A B t)). Qed.
Lemma lem6995026 {A B : Type'} (t : B -> Prop) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (_93258 t) = (term145 A B t).
Proof. exact (EQ_MP (@lem6995025 A B _93258 t) (@lem6995022 A B t _93258 h1)). Qed.
Lemma lem6995027 {A B : Type'} (R : type1413 A B) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem6995028 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (_93258 t R) = (term147 A B t R).
Proof. exact (MK_COMB (@lem6995026 A B t _93258 h1) (@lem6995027 A B R)). Qed.
Lemma lem6995029 {A B : Type'} (t : B -> Prop) (R : type1413 A B) : (term147 A B t R) = (term25 A B t R).
Proof. exact (eq_refl (term147 A B t R)). Qed.
Lemma lem6995030 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term148 A B _93258 t R) = (term148 A B _93258 t R).
Proof. exact (eq_refl (term148 A B _93258 t R)). Qed.
Lemma lem6995031 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) : ((_93258 t R) = (term147 A B t R)) = ((_93258 t R) = (term25 A B t R)).
Proof. exact (MK_COMB (@lem6995030 A B _93258 t R) (@lem6995029 A B t R)). Qed.
Lemma lem6995032 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (_93258 t R) = (term25 A B t R).
Proof. exact (EQ_MP (@lem6995031 A B _93258 t R) (@lem6995028 A B t R _93258 h1)). Qed.
Lemma lem6995033 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6995034 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (_93258 t R x) = (term71 A B t R x).
Proof. exact (MK_COMB (@lem6995032 A B t R _93258 h1) (@lem6995033 A x)). Qed.
Lemma lem6995035 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term71 A B t R x) = (term72 A B t R x).
Proof. exact (eq_refl (term71 A B t R x)). Qed.
Lemma lem6995036 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term149 A B _93258 t R x) = (term149 A B _93258 t R x).
Proof. exact (eq_refl (term149 A B _93258 t R x)). Qed.
Lemma lem6995037 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : ((_93258 t R x) = (term71 A B t R x)) = ((_93258 t R x) = (term72 A B t R x)).
Proof. exact (MK_COMB (@lem6995036 A B _93258 t R x) (@lem6995035 A B t R x)). Qed.
Lemma lem6995038 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (_93258 t R x) = (term72 A B t R x).
Proof. exact (EQ_MP (@lem6995037 A B _93258 t R x) (@lem6995034 A B t R x _93258 h1)). Qed.
Lemma lem6995039 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term72 A B t R x) = (_93258 t R x).
Proof. exact (SYM (@lem6995038 A B t R x _93258 h1)). Qed.
Lemma lem6995040 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : term150 A B _93258 t R.
Proof. exact (fun x : A => @lem6995039 A B t R x _93258 h1). Qed.
Lemma lem6995041 {A B : Type'} (t : B -> Prop) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : term151 A B _93258 t.
Proof. exact (fun R : type1413 A B => @lem6995040 A B t R _93258 h1). Qed.
Lemma lem6995042 {A B : Type'} (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : term152 A B _93258.
Proof. exact (fun t : B -> Prop => @lem6995041 A B t _93258 h1). Qed.
Lemma lem6995043 {A B : Type'} (t : B -> Prop) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : term153 A B _93258 t.
Proof. exact (@lem6995042 A B _93258 h1 t). Qed.
Lemma lem6995044 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) : (term153 A B _93258 t) = (term151 A B _93258 t).
Proof. exact (eq_refl (term153 A B _93258 t)). Qed.
Lemma lem6995045 {A B : Type'} (t : B -> Prop) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : term151 A B _93258 t.
Proof. exact (EQ_MP (@lem6995044 A B _93258 t) (@lem6995043 A B t _93258 h1)). Qed.
Lemma lem6995046 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : term154 A B _93258 t R.
Proof. exact (@lem6995045 A B t _93258 h1 R). Qed.
Lemma lem6995047 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term154 A B _93258 t R) = (term150 A B _93258 t R).
Proof. exact (eq_refl (term154 A B _93258 t R)). Qed.
Lemma lem6995048 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : term150 A B _93258 t R.
Proof. exact (EQ_MP (@lem6995047 A B _93258 t R) (@lem6995046 A B t R _93258 h1)). Qed.
Lemma lem6995049 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : term155 A B _93258 t R x.
Proof. exact (@lem6995048 A B t R _93258 h1 x). Qed.
Lemma lem6995050 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term155 A B _93258 t R x) = ((term72 A B t R x) = (_93258 t R x)).
Proof. exact (eq_refl (term155 A B _93258 t R x)). Qed.
Lemma lem6995053 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term72 A B t R x) = (_93258 t R x).
Proof. exact (EQ_MP (@lem6995050 A B _93258 t R x) (@lem6995049 A B t R x _93258 h1)). Qed.
Lemma lem6995054 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term72 A B t R x) = (_93258 t R x).
Proof. exact (@lem6995053 A B t R x _93258 h1). Qed.
Lemma lem6995055 {B : Type'} : (@IN B) = (@IN B).
Proof. exact (eq_refl (@IN B)). Qed.
Lemma lem6995056 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term77 A B t R x) = (term156 A B _93258 t R x).
Proof. exact (MK_COMB (@lem6995055 B) (@lem6995054 A B t R x _93258 h1)). Qed.
Lemma lem6995057 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem6995058 {A B : Type'} (R : type1413 A B) (x : A) (t : B -> Prop) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term78 A B R x t) = (term157 A B _93258 R x t).
Proof. exact (MK_COMB (@lem6995056 A B t R x _93258 h1) (@lem6995057 B t)). Qed.
Lemma lem6995059 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6995060 {A B : Type'} (R : type1413 A B) (x : A) (t : B -> Prop) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term158 A B R x t) = (term159 A B _93258 R x t).
Proof. exact (MK_COMB (@lem6995059) (@lem6995058 A B R x t _93258 h1)). Qed.
Lemma lem6995062 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term72 A B t R x) = (_93258 t R x).
Proof. exact (EQ_MP (@lem6995050 A B _93258 t R x) (@lem6995049 A B t R x _93258 h1)). Qed.
Lemma lem6995063 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term72 A B t R x) = (_93258 t R x).
Proof. exact (@lem6995062 A B t R x _93258 h1). Qed.
Lemma lem6995064 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (R x).
Proof. exact (eq_refl (R x)). Qed.
Lemma lem6995065 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term160 A B t R x) = (term161 A B _93258 t R x).
Proof. exact (MK_COMB (@lem6995064 A B R x) (@lem6995063 A B t R x _93258 h1)). Qed.
Lemma lem6995066 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term127 A B t R x) = (term162 A B _93258 t R x).
Proof. exact (MK_COMB (@lem6995060 A B R x t _93258 h1) (@lem6995065 A B t R x _93258 h1)). Qed.
Lemma lem6995067 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term131 A B t R x x') = (term131 A B t R x x').
Proof. exact (eq_refl (term131 A B t R x x')). Qed.
Lemma lem6995068 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (x' : A) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term133 A B x t R x') = (term163 A B x _93258 t R x').
Proof. exact (MK_COMB (@lem6995067 A B t R x' x) (@lem6995066 A B t R x' _93258 h1)). Qed.
Lemma lem6995069 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term135 A B t R x) = (term164 A B _93258 t R x).
Proof. exact (fun_ext (fun x' : B => @lem6995068 A B x' t R x _93258 h1)). Qed.
Lemma lem6995070 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6995071 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term136 A B t R x) = (term165 A B _93258 t R x).
Proof. exact (MK_COMB (@lem6995070 B) (@lem6995069 A B t R x _93258 h1)). Qed.
Lemma lem6995072 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term166 A B t R) = (term167 A B _93258 t R).
Proof. exact (fun_ext (fun x : A => @lem6995071 A B t R x _93258 h1)). Qed.
Lemma lem6995073 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6995074 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term137 A B t R) = (term168 A B _93258 t R).
Proof. exact (MK_COMB (@lem6995073 A) (@lem6995072 A B t R _93258 h1)). Qed.
Lemma lem6995075 {A B : Type'} (t : B -> Prop) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term169 A B t) = (term170 A B _93258 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem6995074 A B t R _93258 h1)). Qed.
Lemma lem6995076 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem6995077 {A B : Type'} (t : B -> Prop) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term138 A B t) = (term171 A B _93258 t).
Proof. exact (MK_COMB (@lem6995076 A B) (@lem6995075 A B t _93258 h1)). Qed.
Lemma lem6995078 {A B : Type'} (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term172 A B) = (term173 A B _93258).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6995077 A B t _93258 h1)). Qed.
Lemma lem6995079 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6995080 {A B : Type'} (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term139 A B) = (term174 A B _93258).
Proof. exact (MK_COMB (@lem6995079 B) (@lem6995078 A B _93258 h1)). Qed.
Lemma lem6995081 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6995082 {A B : Type'} (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term175 A B) = (term176 A B _93258).
Proof. exact (MK_COMB (@lem6995081) (@lem6995080 A B _93258 h1)). Qed.
Lemma lem6995084 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term72 A B t R x) = (_93258 t R x).
Proof. exact (EQ_MP (@lem6995050 A B _93258 t R x) (@lem6995049 A B t R x _93258 h1)). Qed.
Lemma lem6995085 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term72 A B t R x) = (_93258 t R x).
Proof. exact (@lem6995084 A B t R x _93258 h1). Qed.
Lemma lem6995086 {B : Type'} : (@IN B) = (@IN B).
Proof. exact (eq_refl (@IN B)). Qed.
Lemma lem6995087 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term77 A B t R x) = (term156 A B _93258 t R x).
Proof. exact (MK_COMB (@lem6995086 B) (@lem6995085 A B t R x _93258 h1)). Qed.
Lemma lem6995088 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem6995089 {A B : Type'} (R : type1413 A B) (x : A) (t : B -> Prop) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term78 A B R x t) = (term157 A B _93258 R x t).
Proof. exact (MK_COMB (@lem6995087 A B t R x _93258 h1) (@lem6995088 B t)). Qed.
Lemma lem6995090 {A : Type'} (x : A) (s : A -> Prop) : (term63 A x s) = (term63 A x s).
Proof. exact (eq_refl (term63 A x s)). Qed.
Lemma lem6995091 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : A) (t : B -> Prop) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term79 A B s R x t) = (term177 A B s _93258 R x t).
Proof. exact (MK_COMB (@lem6995090 A x s) (@lem6995089 A B R x t _93258 h1)). Qed.
Lemma lem6995092 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term80 A B s R t) = (term178 A B s _93258 R t).
Proof. exact (fun_ext (fun x : A => @lem6995091 A B s R x t _93258 h1)). Qed.
Lemma lem6995093 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6995094 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term81 A B s R t) = (term179 A B s _93258 R t).
Proof. exact (MK_COMB (@lem6995093 A) (@lem6995092 A B s R t _93258 h1)). Qed.
Lemma lem6995095 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6995096 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term122 A B s R t) = (term180 A B s _93258 R t).
Proof. exact (MK_COMB (@lem6995095) (@lem6995094 A B s R t _93258 h1)). Qed.
Lemma lem6995097 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6995098 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term181 A B s R t) = (term182 A B s _93258 R t).
Proof. exact (MK_COMB (@lem6995097) (@lem6995096 A B s R t _93258 h1)). Qed.
Lemma lem6995099 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem6995100 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term121 A B s R t) = (term183 A B s _93258 R t).
Proof. exact (MK_COMB (@lem6995098 A B s R t _93258 h1) (@lem6995099)). Qed.
Lemma lem6995101 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term184 A B s t R) = (term184 A B s t R).
Proof. exact (eq_refl (term184 A B s t R)). Qed.
Lemma lem6995102 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term185 A B s R t) = (term186 A B s _93258 R t).
Proof. exact (MK_COMB (@lem6995101 A B s t R) (@lem6995100 A B s R t _93258 h1)). Qed.
Lemma lem6995103 {A : Type'} (s : A -> Prop) : (term187 A s) = (term187 A s).
Proof. exact (eq_refl (term187 A s)). Qed.
Lemma lem6995104 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term141 A B s R t) = (term188 A B s _93258 R t).
Proof. exact (MK_COMB (@lem6995103 A s) (@lem6995102 A B s R t _93258 h1)). Qed.
Lemma lem6995105 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term140 A B s R t) = (term189 A B s _93258 R t).
Proof. exact (MK_COMB (@lem6995082 A B _93258 h1) (@lem6995104 A B s R t _93258 h1)). Qed.
Lemma lem6995106 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term190 A B s R t) : term190 A B s R t.
Proof. exact (h1). Qed.
Lemma lem6995107 {A B : Type'} (_93258 : type830 A B) (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term190 A B s R t) : term191 A B s R t _93258.
Proof. exact (@lem6995106 A B s R t h1 _93258). Qed.
Lemma lem6995108 {A B : Type'} (s : A -> Prop) (_93258 : type830 A B) (R : type1413 A B) (t : B -> Prop) : (term191 A B s R t _93258) = (term189 A B s _93258 R t).
Proof. exact (eq_refl (term191 A B s R t _93258)). Qed.
Lemma lem6995109 {A B : Type'} (_93258 : type830 A B) (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term190 A B s R t) : term189 A B s _93258 R t.
Proof. exact (EQ_MP (@lem6995108 A B s _93258 R t) (@lem6995107 A B _93258 s R t h1)). Qed.
Lemma lem6995110 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : (term189 A B s _93258 R t) = (term140 A B s R t).
Proof. exact (SYM (@lem6995105 A B s R t _93258 h1)). Qed.
Lemma lem6995111 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_93258 : type830 A B) (h1 : term190 A B s R t) (h2 : _93258 = (term143 A B)) : term140 A B s R t.
Proof. exact (EQ_MP (@lem6995110 A B s R t _93258 h2) (@lem6995109 A B _93258 s R t h1)). Qed.
Lemma lem6995112 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : term192 A B s R t.
Proof. exact (fun h0 : term190 A B s R t => @lem6995111 A B s R t _93258 h0 h1). Qed.
Lemma lem6995113 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term193 A B s R t.
Proof. exact (@lem51 (term140 A B s R t) (term190 A B s R t) (term141 A B s R t)). Qed.
Lemma lem6995114 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : term194 A B s R t.
Proof. exact (@lem6995113 A B s R t (@lem6995112 A B s R t _93258 h1)). Qed.
Lemma lem6995115 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_93258 : type830 A B) (h1 : _93258 = (term143 A B)) : term195 A B s R t.
Proof. exact (@lem6995114 A B s R t _93258 h1 (@lem6995019 A B s R t)). Qed.
Lemma lem6995116 {A B : Type'} : (term143 A B) = (term143 A B).
Proof. exact (eq_refl (term143 A B)). Qed.
Lemma lem6995117 {A B : Type'} (_93258 : type830 A B) (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term196 A B _93258 s R t.
Proof. exact (fun h0 : _93258 = (term143 A B) => @lem6995115 A B s R t _93258 h0). Qed.
Lemma lem6995118 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term197 A B s R t.
Proof. exact (@lem6995117 A B (term143 A B) s R t). Qed.
Lemma lem6995119 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term195 A B s R t.
Proof. exact (@lem6995118 A B s R t (@lem6995116 A B)). Qed.
Lemma lem6995120 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term190 A B s R t) : term190 A B s R t.
Proof. exact (h1). Qed.
Lemma lem6995121 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term198 A B s R t.
Proof. exact (fun h0 : term190 A B s R t => @lem6995120 A B s R t h0). Qed.
Lemma lem6995122 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term199 A B s R t.
Proof. exact (@lem51 (term190 A B s R t) (term190 A B s R t) (term141 A B s R t)). Qed.
Lemma lem6995123 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term200 A B s R t.
Proof. exact (@lem6995122 A B s R t (@lem6995121 A B s R t)). Qed.
Lemma lem6995124 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term195 A B s R t.
Proof. exact (@lem6995123 A B s R t (@lem6995119 A B s R t)). Qed.
Lemma lem6995125 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term195 A B s R t) : term195 A B s R t.
Proof. exact (h1). Qed.
Lemma lem6995126 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term190 A B s R t) : term190 A B s R t.
Proof. exact (h1). Qed.
Lemma lem6995127 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term190 A B s R t) (h2 : term195 A B s R t) : term141 A B s R t.
Proof. exact (@lem6995125 A B s R t h2 (@lem6995126 A B s R t h1)). Qed.
Lemma lem6995128 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term190 A B s R t) : term201 A B s R t.
Proof. exact (fun h0 : term195 A B s R t => @lem6995127 A B s R t h1 h0). Qed.
Lemma lem6995129 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term195 A B s R t) : term195 A B s R t.
Proof. exact (h1). Qed.
Lemma lem6995130 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term190 A B s R t) (h2 : term195 A B s R t) : term141 A B s R t.
Proof. exact (@lem6995128 A B s R t h1 (@lem6995129 A B s R t h2)). Qed.
Lemma lem6995131 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term195 A B s R t) : term195 A B s R t.
Proof. exact (fun h0 : term190 A B s R t => @lem6995130 A B s R t h0 h1). Qed.
Lemma lem6995132 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term200 A B s R t.
Proof. exact (fun h0 : term195 A B s R t => @lem6995131 A B s R t h0). Qed.
Lemma lem6995135 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term195 A B s R t.
Proof. exact (@lem6995132 A B s R t (@lem6995124 A B s R t)). Qed.
Lemma lem6995136 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term195 A B s R t.
Proof. exact (@lem6995135 A B s R t). Qed.
Lemma lem6995190 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6995191 {A B : Type'} (s : A -> Prop) (_93258 : type830 A B) (R : type1413 A B) (t : B -> Prop) : (term183 A B s _93258 R t) = (term202 A B s _93258 R t).
Proof. exact (@lem6995190 (term180 A B s _93258 R t)). Qed.
Lemma lem6995193 (t : Prop) : (term203 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6995194 {A B : Type'} (s : A -> Prop) (_93258 : type830 A B) (R : type1413 A B) (t : B -> Prop) : (term202 A B s _93258 R t) = (term179 A B s _93258 R t).
Proof. exact (@lem6995193 (term179 A B s _93258 R t)). Qed.
Lemma lem6995199 {A B : Type'} (s : A -> Prop) (_93258 : type830 A B) (R : type1413 A B) (t : B -> Prop) : (term183 A B s _93258 R t) = (term179 A B s _93258 R t).
Proof. exact (TRANS (@lem6995191 A B s _93258 R t) (@lem6995194 A B s _93258 R t)). Qed.
Lemma lem6995202 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term184 A B s t R) = (term184 A B s t R).
Proof. exact (eq_refl (term184 A B s t R)). Qed.
Lemma lem6995203 {A B : Type'} (s : A -> Prop) (_93258 : type830 A B) (R : type1413 A B) (t : B -> Prop) : (term186 A B s _93258 R t) = (term204 A B s _93258 R t).
Proof. exact (MK_COMB (@lem6995202 A B s t R) (@lem6995199 A B s _93258 R t)). Qed.
Lemma lem6995206 {A : Type'} (s : A -> Prop) : (term187 A s) = (term187 A s).
Proof. exact (eq_refl (term187 A s)). Qed.
Lemma lem6995207 {A B : Type'} (s : A -> Prop) (_93258 : type830 A B) (R : type1413 A B) (t : B -> Prop) : (term188 A B s _93258 R t) = (term205 A B s _93258 R t).
Proof. exact (MK_COMB (@lem6995206 A s) (@lem6995203 A B s _93258 R t)). Qed.
Lemma lem6995210 {A B : Type'} (_93258 : type830 A B) : (term176 A B _93258) = (term176 A B _93258).
Proof. exact (eq_refl (term176 A B _93258)). Qed.
Lemma lem6995211 {A B : Type'} (s : A -> Prop) (_93258 : type830 A B) (R : type1413 A B) (t : B -> Prop) : (term189 A B s _93258 R t) = (term206 A B s _93258 R t).
Proof. exact (MK_COMB (@lem6995210 A B _93258) (@lem6995207 A B s _93258 R t)). Qed.
Lemma lem6995214 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term207 A B s R t) = (term208 A B s R t).
Proof. exact (fun_ext (fun _93258 : type830 A B => @lem6995211 A B s _93258 R t)). Qed.
Lemma lem6995215 {A B : Type'} : (@all ((B -> Prop) -> (A -> B -> Prop) -> A -> B)) = (@all ((B -> Prop) -> (A -> B -> Prop) -> A -> B)).
Proof. exact (eq_refl (@all ((B -> Prop) -> (A -> B -> Prop) -> A -> B))). Qed.
Lemma lem6995216 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term190 A B s R t) = (term209 A B s R t).
Proof. exact (MK_COMB (@lem6995215 A B) (@lem6995214 A B s R t)). Qed.
Lemma lem6995221 {A B : Type'} (R : type1413 A B) (t : B -> Prop) : (term210 A B R t) = (term211 A B R t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6995216 A B s R t)). Qed.
Lemma lem6995222 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6995223 {A B : Type'} (R : type1413 A B) (t : B -> Prop) : (term212 A B R t) = (term213 A B R t).
Proof. exact (MK_COMB (@lem6995222 A) (@lem6995221 A B R t)). Qed.
Lemma lem6995228 {A B : Type'} (t : B -> Prop) : (term214 A B t) = (term215 A B t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem6995223 A B R t)). Qed.
Lemma lem6995229 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem6995230 {A B : Type'} (t : B -> Prop) : (term216 A B t) = (term217 A B t).
Proof. exact (MK_COMB (@lem6995229 A B) (@lem6995228 A B t)). Qed.
Lemma lem6995235 {A B : Type'} : (term218 A B) = (term219 A B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6995230 A B t)). Qed.
Lemma lem6995236 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6995245 {A B : Type'} : (term220 A B) = (term221 A B).
Proof. exact (MK_COMB (@lem6995236 B) (@lem6995235 A B)). Qed.
Lemma lem6995250 {A B : Type'} (s : A -> Prop) (_93258 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term177 A B s _93258 R x t) = (term177 A B s _93258 R x t).
Proof. exact (eq_refl (term177 A B s _93258 R x t)). Qed.
Lemma lem6995251 {A B : Type'} (s : A -> Prop) (_93258 : type830 A B) (R : type1413 A B) (t : B -> Prop) : (term178 A B s _93258 R t) = (term178 A B s _93258 R t).
Proof. exact (fun_ext (fun x : A => @lem6995250 A B s _93258 R x t)). Qed.
Lemma lem6995252 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6995253 {A B : Type'} (s : A -> Prop) (_93258 : type830 A B) (R : type1413 A B) (t : B -> Prop) : (term179 A B s _93258 R t) = (term179 A B s _93258 R t).
Proof. exact (MK_COMB (@lem6995252 A) (@lem6995251 A B s _93258 R t)). Qed.
Lemma lem6995258 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term129 A B t R x y) = (term129 A B t R x y).
Proof. exact (eq_refl (term129 A B t R x y)). Qed.
Lemma lem6995259 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term125 A B t R x) = (term125 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem6995258 A B t R x y)). Qed.
Lemma lem6995260 {B : Type'} : (@ex1 B) = (@ex1 B).
Proof. exact (eq_refl (@ex1 B)). Qed.
Lemma lem6995261 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term222 A B t R x) = (term222 A B t R x).
Proof. exact (MK_COMB (@lem6995260 B) (@lem6995259 A B t R x)). Qed.
Lemma lem6995264 {A : Type'} (x : A) (s : A -> Prop) : (term63 A x s) = (term63 A x s).
Proof. exact (eq_refl (term63 A x s)). Qed.
Lemma lem6995265 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term223 A B s t R x) = (term223 A B s t R x).
Proof. exact (MK_COMB (@lem6995264 A x s) (@lem6995261 A B t R x)). Qed.
Lemma lem6995266 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term224 A B s t R) = (term224 A B s t R).
Proof. exact (fun_ext (fun x : A => @lem6995265 A B s t R x)). Qed.
Lemma lem6995267 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6995268 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term34 A B s t R) = (term34 A B s t R).
Proof. exact (MK_COMB (@lem6995267 A) (@lem6995266 A B s t R)). Qed.
Lemma lem6995269 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6995270 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term184 A B s t R) = (term184 A B s t R).
Proof. exact (MK_COMB (@lem6995269) (@lem6995268 A B s t R)). Qed.
Lemma lem6995271 {A B : Type'} (s : A -> Prop) (_93258 : type830 A B) (R : type1413 A B) (t : B -> Prop) : (term204 A B s _93258 R t) = (term204 A B s _93258 R t).
Proof. exact (MK_COMB (@lem6995270 A B s t R) (@lem6995253 A B s _93258 R t)). Qed.
Lemma lem6995274 {A : Type'} (s : A -> Prop) : (term187 A s) = (term187 A s).
Proof. exact (eq_refl (term187 A s)). Qed.
Lemma lem6995275 {A B : Type'} (s : A -> Prop) (_93258 : type830 A B) (R : type1413 A B) (t : B -> Prop) : (term205 A B s _93258 R t) = (term205 A B s _93258 R t).
Proof. exact (MK_COMB (@lem6995274 A s) (@lem6995271 A B s _93258 R t)). Qed.
Lemma lem6995288 {A B : Type'} (x : B) (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term163 A B x _93258 t R x') = (term163 A B x _93258 t R x').
Proof. exact (eq_refl (term163 A B x _93258 t R x')). Qed.
Lemma lem6995289 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term164 A B _93258 t R x) = (term164 A B _93258 t R x).
Proof. exact (fun_ext (fun x' : B => @lem6995288 A B x' _93258 t R x)). Qed.
Lemma lem6995290 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6995291 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term165 A B _93258 t R x) = (term165 A B _93258 t R x).
Proof. exact (MK_COMB (@lem6995290 B) (@lem6995289 A B _93258 t R x)). Qed.
Lemma lem6995292 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term167 A B _93258 t R) = (term167 A B _93258 t R).
Proof. exact (fun_ext (fun x : A => @lem6995291 A B _93258 t R x)). Qed.
Lemma lem6995293 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6995294 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term168 A B _93258 t R) = (term168 A B _93258 t R).
Proof. exact (MK_COMB (@lem6995293 A) (@lem6995292 A B _93258 t R)). Qed.
Lemma lem6995295 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) : (term170 A B _93258 t) = (term170 A B _93258 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem6995294 A B _93258 t R)). Qed.
Lemma lem6995296 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem6995297 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) : (term171 A B _93258 t) = (term171 A B _93258 t).
Proof. exact (MK_COMB (@lem6995296 A B) (@lem6995295 A B _93258 t)). Qed.
Lemma lem6995298 {A B : Type'} (_93258 : type830 A B) : (term173 A B _93258) = (term173 A B _93258).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6995297 A B _93258 t)). Qed.
Lemma lem6995299 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6995300 {A B : Type'} (_93258 : type830 A B) : (term174 A B _93258) = (term174 A B _93258).
Proof. exact (MK_COMB (@lem6995299 B) (@lem6995298 A B _93258)). Qed.
Lemma lem6995301 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6995302 {A B : Type'} (_93258 : type830 A B) : (term176 A B _93258) = (term176 A B _93258).
Proof. exact (MK_COMB (@lem6995301) (@lem6995300 A B _93258)). Qed.
Lemma lem6995303 {A B : Type'} (s : A -> Prop) (_93258 : type830 A B) (R : type1413 A B) (t : B -> Prop) : (term206 A B s _93258 R t) = (term206 A B s _93258 R t).
Proof. exact (MK_COMB (@lem6995302 A B _93258) (@lem6995275 A B s _93258 R t)). Qed.
Lemma lem6995304 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term208 A B s R t) = (term208 A B s R t).
Proof. exact (fun_ext (fun _93258 : type830 A B => @lem6995303 A B s _93258 R t)). Qed.
Lemma lem6995305 {A B : Type'} : (@all ((B -> Prop) -> (A -> B -> Prop) -> A -> B)) = (@all ((B -> Prop) -> (A -> B -> Prop) -> A -> B)).
Proof. exact (eq_refl (@all ((B -> Prop) -> (A -> B -> Prop) -> A -> B))). Qed.
Lemma lem6995306 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term209 A B s R t) = (term209 A B s R t).
Proof. exact (MK_COMB (@lem6995305 A B) (@lem6995304 A B s R t)). Qed.
Lemma lem6995307 {A B : Type'} (R : type1413 A B) (t : B -> Prop) : (term211 A B R t) = (term211 A B R t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6995306 A B s R t)). Qed.
Lemma lem6995308 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6995309 {A B : Type'} (R : type1413 A B) (t : B -> Prop) : (term213 A B R t) = (term213 A B R t).
Proof. exact (MK_COMB (@lem6995308 A) (@lem6995307 A B R t)). Qed.
Lemma lem6995310 {A B : Type'} (t : B -> Prop) : (term215 A B t) = (term215 A B t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem6995309 A B R t)). Qed.
Lemma lem6995311 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem6995312 {A B : Type'} (t : B -> Prop) : (term217 A B t) = (term217 A B t).
Proof. exact (MK_COMB (@lem6995311 A B) (@lem6995310 A B t)). Qed.
Lemma lem6995313 {A B : Type'} : (term219 A B) = (term219 A B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6995312 A B t)). Qed.
Lemma lem6995314 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6995315 {A B : Type'} : (term221 A B) = (term221 A B).
Proof. exact (MK_COMB (@lem6995314 B) (@lem6995313 A B)). Qed.
Lemma lem6995396 {A B : Type'} : (term220 A B) = (term221 A B).
Proof. exact (TRANS (@lem6995245 A B) (@lem6995315 A B)). Qed.
Lemma lem6995397 {A B : Type'} : (term221 A B) = (term220 A B).
Proof. exact (SYM (@lem6995396 A B)). Qed.
Lemma lem6995398 {A B : Type'} (_93258 : type830 A B) (h1 : term174 A B _93258) : term174 A B _93258.
Proof. exact (h1). Qed.
Lemma lem6995400 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (h1 : term34 A B s t R) : term34 A B s t R.
Proof. exact (h1). Qed.
Lemma lem6995403 (p : Prop) : p = (term120 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6995404 {A B : Type'} (_93258 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term157 A B _93258 R x t) = (term225 A B _93258 R x t).
Proof. exact (@lem6995403 (term157 A B _93258 R x t)). Qed.
Lemma lem6995405 {A B : Type'} (_93258 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term225 A B _93258 R x t) = (term157 A B _93258 R x t).
Proof. exact (SYM (@lem6995404 A B _93258 R x t)). Qed.
Lemma lem6995406 {A B : Type'} (_93258 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) (h1 : term226 A B _93258 R x t) : term226 A B _93258 R x t.
Proof. exact (h1). Qed.
Lemma lem6995413 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term227 A B t R x x') = (term228 A B t R x x').
Proof. exact (@lem17045 (@IN B x' t) (R x x')). Qed.
Lemma lem6995418 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term162 A B _93258 t R x) = (term162 A B _93258 t R x).
Proof. exact (eq_refl (term162 A B _93258 t R x)). Qed.
Lemma lem6995419 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6995420 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term229 A B t R x x') = (term230 A B t R x x').
Proof. exact (MK_COMB (@lem6995419) (@lem6995413 A B t R x x')). Qed.
Lemma lem6995421 {A B : Type'} (x : B) (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term231 A B x _93258 t R x') = (term232 A B x _93258 t R x').
Proof. exact (MK_COMB (@lem6995420 A B t R x' x) (@lem6995418 A B _93258 t R x')). Qed.
Lemma lem6995422 {A B : Type'} (x : B) (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term163 A B x _93258 t R x') = (term231 A B x _93258 t R x').
Proof. exact (@lem17265 (term129 A B t R x' x) (term162 A B _93258 t R x')). Qed.
Lemma lem6995423 {A B : Type'} (x : B) (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term163 A B x _93258 t R x') = (term232 A B x _93258 t R x').
Proof. exact (TRANS (@lem6995422 A B x _93258 t R x') (@lem6995421 A B x _93258 t R x')). Qed.
Lemma lem6995424 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term164 A B _93258 t R x) = (term233 A B _93258 t R x).
Proof. exact (fun_ext (fun x' : B => @lem6995423 A B x' _93258 t R x)). Qed.
Lemma lem6995425 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6995426 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term165 A B _93258 t R x) = (term234 A B _93258 t R x).
Proof. exact (MK_COMB (@lem6995425 B) (@lem6995424 A B _93258 t R x)). Qed.
Lemma lem6995427 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term167 A B _93258 t R) = (term235 A B _93258 t R).
Proof. exact (fun_ext (fun x : A => @lem6995426 A B _93258 t R x)). Qed.
Lemma lem6995428 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6995429 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term168 A B _93258 t R) = (term236 A B _93258 t R).
Proof. exact (MK_COMB (@lem6995428 A) (@lem6995427 A B _93258 t R)). Qed.
Lemma lem6995430 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) : (term170 A B _93258 t) = (term237 A B _93258 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem6995429 A B _93258 t R)). Qed.
Lemma lem6995431 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem6995432 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) : (term171 A B _93258 t) = (term238 A B _93258 t).
Proof. exact (MK_COMB (@lem6995431 A B) (@lem6995430 A B _93258 t)). Qed.
Lemma lem6995433 {A B : Type'} (_93258 : type830 A B) : (term173 A B _93258) = (term239 A B _93258).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6995432 A B _93258 t)). Qed.
Lemma lem6995434 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6995435 {A B : Type'} (_93258 : type830 A B) : (term174 A B _93258) = (term240 A B _93258).
Proof. exact (MK_COMB (@lem6995434 B) (@lem6995433 A B _93258)). Qed.
Lemma lem6995469 {A : Type'} (P : A -> Prop) (Q : Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem6995470 {B : Type'} (P : B -> Prop) (Q : Prop) : (term241 B P Q) = (term242 B P Q).
Proof. exact (@lem6995469 B P Q). Qed.
Lemma lem6995471 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term243 A B _93258 t R x) = (term244 A B _93258 t R x).
Proof. exact (@lem6995470 B (term245 A B t R x) (term162 A B _93258 t R x)). Qed.
Lemma lem6995472 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term246 A B t R x x') = (term228 A B t R x x').
Proof. exact (eq_refl (term246 A B t R x x')). Qed.
Lemma lem6995473 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6995474 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term247 A B t R x x') = (term230 A B t R x x').
Proof. exact (MK_COMB (@lem6995473) (@lem6995472 A B t R x x')). Qed.
Lemma lem6995475 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term162 A B _93258 t R x) = (term162 A B _93258 t R x).
Proof. exact (eq_refl (term162 A B _93258 t R x)). Qed.
Lemma lem6995476 {A B : Type'} (x : B) (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term248 A B x _93258 t R x') = (term232 A B x _93258 t R x').
Proof. exact (MK_COMB (@lem6995474 A B t R x' x) (@lem6995475 A B _93258 t R x')). Qed.
Lemma lem6995477 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term249 A B _93258 t R x) = (term233 A B _93258 t R x).
Proof. exact (fun_ext (fun x' : B => @lem6995476 A B x' _93258 t R x)). Qed.
Lemma lem6995478 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6995479 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term243 A B _93258 t R x) = (term234 A B _93258 t R x).
Proof. exact (MK_COMB (@lem6995478 B) (@lem6995477 A B _93258 t R x)). Qed.
Lemma lem6995480 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6995481 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term250 A B _93258 t R x) = (term251 A B _93258 t R x).
Proof. exact (MK_COMB (@lem6995480) (@lem6995479 A B _93258 t R x)). Qed.
Lemma lem6995482 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term246 A B t R x x') = (term228 A B t R x x').
Proof. exact (eq_refl (term246 A B t R x x')). Qed.
Lemma lem6995483 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term252 A B t R x) = (term245 A B t R x).
Proof. exact (fun_ext (fun x' : B => @lem6995482 A B t R x x')). Qed.
Lemma lem6995484 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6995485 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term253 A B t R x) = (term254 A B t R x).
Proof. exact (MK_COMB (@lem6995484 B) (@lem6995483 A B t R x)). Qed.
Lemma lem6995486 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6995487 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term255 A B t R x) = (term256 A B t R x).
Proof. exact (MK_COMB (@lem6995486) (@lem6995485 A B t R x)). Qed.
Lemma lem6995488 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term162 A B _93258 t R x) = (term162 A B _93258 t R x).
Proof. exact (eq_refl (term162 A B _93258 t R x)). Qed.
Lemma lem6995489 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term244 A B _93258 t R x) = (term257 A B _93258 t R x).
Proof. exact (MK_COMB (@lem6995487 A B t R x) (@lem6995488 A B _93258 t R x)). Qed.
Lemma lem6995490 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : ((term243 A B _93258 t R x) = (term244 A B _93258 t R x)) = ((term234 A B _93258 t R x) = (term257 A B _93258 t R x)).
Proof. exact (MK_COMB (@lem6995481 A B _93258 t R x) (@lem6995489 A B _93258 t R x)). Qed.
Lemma lem6995491 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term234 A B _93258 t R x) = (term257 A B _93258 t R x).
Proof. exact (EQ_MP (@lem6995490 A B _93258 t R x) (@lem6995471 A B _93258 t R x)). Qed.
Lemma lem6995540 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term235 A B _93258 t R) = (term258 A B _93258 t R).
Proof. exact (fun_ext (fun x : A => @lem6995491 A B _93258 t R x)). Qed.
Lemma lem6995541 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6995542 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term236 A B _93258 t R) = (term259 A B _93258 t R).
Proof. exact (MK_COMB (@lem6995541 A) (@lem6995540 A B _93258 t R)). Qed.
Lemma lem6995591 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) : (term237 A B _93258 t) = (term260 A B _93258 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem6995542 A B _93258 t R)). Qed.
Lemma lem6995592 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem6995593 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) : (term238 A B _93258 t) = (term261 A B _93258 t).
Proof. exact (MK_COMB (@lem6995592 A B) (@lem6995591 A B _93258 t)). Qed.
Lemma lem6995598 {A B : Type'} (_93258 : type830 A B) : (term239 A B _93258) = (term262 A B _93258).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6995593 A B _93258 t)). Qed.
Lemma lem6995599 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6995606 {A B : Type'} (_93258 : type830 A B) : (term240 A B _93258) = (term263 A B _93258).
Proof. exact (MK_COMB (@lem6995599 B) (@lem6995598 A B _93258)). Qed.
Lemma lem6995607 {A B : Type'} (_93258 : type830 A B) : (term174 A B _93258) = (term263 A B _93258).
Proof. exact (TRANS (@lem6995435 A B _93258) (@lem6995606 A B _93258)). Qed.
Lemma lem6995608 {A B : Type'} (_93258 : type830 A B) (h1 : term174 A B _93258) : term263 A B _93258.
Proof. exact (EQ_MP (@lem6995607 A B _93258) (@lem6995398 A B _93258 h1)). Qed.
Lemma lem6995624 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term227 A B t R x y) = (term228 A B t R x y).
Proof. exact (@lem17045 (@IN B y t) (R x y)). Qed.
Lemma lem6995629 {B : Type'} (y' : B) (y : B) : (y' = y) = (y' = y).
Proof. exact (eq_refl (y' = y)). Qed.
Lemma lem6995630 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term128 A B t R x y) = (term129 A B t R x y).
Proof. exact (eq_refl (term128 A B t R x y)). Qed.
Lemma lem6995631 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term128 A B t R x y') = (term129 A B t R x y').
Proof. exact (eq_refl (term128 A B t R x y')). Qed.
Lemma lem6995632 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term227 A B t R x y') = (term228 A B t R x y').
Proof. exact (@lem6995624 A B t R x y'). Qed.
Lemma lem6995633 {B : Type'} (P : B -> Prop) : (@ex1 B P) = (term264 B P).
Proof. exact (@lem18897 B P). Qed.
Lemma lem6995634 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term222 A B t R x) = (term265 A B t R x).
Proof. exact (@lem6995633 B (term125 A B t R x)). Qed.
Lemma lem6995635 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6995636 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term266 A B t R x y') = (term227 A B t R x y').
Proof. exact (MK_COMB (@lem6995635) (@lem6995631 A B t R x y')). Qed.
Lemma lem6995637 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term266 A B t R x y') = (term228 A B t R x y').
Proof. exact (TRANS (@lem6995636 A B t R x y') (@lem6995632 A B t R x y')). Qed.
Lemma lem6995638 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6995639 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term267 A B t R x y') = (term230 A B t R x y').
Proof. exact (MK_COMB (@lem6995638) (@lem6995637 A B t R x y')). Qed.
Lemma lem6995640 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term268 A B t R x y' y) = (term269 A B t R x y' y).
Proof. exact (MK_COMB (@lem6995639 A B t R x y') (@lem6995629 B y' y)). Qed.
Lemma lem6995641 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6995642 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term266 A B t R x y) = (term227 A B t R x y).
Proof. exact (MK_COMB (@lem6995641) (@lem6995630 A B t R x y)). Qed.
Lemma lem6995643 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term266 A B t R x y) = (term228 A B t R x y).
Proof. exact (TRANS (@lem6995642 A B t R x y) (@lem6995624 A B t R x y)). Qed.
Lemma lem6995644 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6995645 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term267 A B t R x y) = (term230 A B t R x y).
Proof. exact (MK_COMB (@lem6995644) (@lem6995643 A B t R x y)). Qed.
Lemma lem6995646 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term270 A B t R x y' y) = (term271 A B t R x y' y).
Proof. exact (MK_COMB (@lem6995645 A B t R x y) (@lem6995640 A B t R x y' y)). Qed.
Lemma lem6995647 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term272 A B t R x y) = (term273 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem6995646 A B t R x y' y)). Qed.
Lemma lem6995648 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6995649 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term274 A B t R x y) = (term275 A B t R x y).
Proof. exact (MK_COMB (@lem6995648 B) (@lem6995647 A B t R x y)). Qed.
Lemma lem6995650 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term276 A B t R x) = (term277 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem6995649 A B t R x y)). Qed.
Lemma lem6995651 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6995652 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term278 A B t R x) = (term279 A B t R x).
Proof. exact (MK_COMB (@lem6995651 B) (@lem6995650 A B t R x)). Qed.
Lemma lem6995653 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term128 A B t R x y) = (term129 A B t R x y).
Proof. exact (eq_refl (term128 A B t R x y)). Qed.
Lemma lem6995654 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term280 A B t R x) = (term125 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem6995653 A B t R x y)). Qed.
Lemma lem6995655 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6995656 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term281 A B t R x) = (term282 A B t R x).
Proof. exact (MK_COMB (@lem6995655 B) (@lem6995654 A B t R x)). Qed.
Lemma lem6995657 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6995658 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term283 A B t R x) = (term284 A B t R x).
Proof. exact (MK_COMB (@lem6995657) (@lem6995656 A B t R x)). Qed.
Lemma lem6995659 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term265 A B t R x) = (term285 A B t R x).
Proof. exact (MK_COMB (@lem6995658 A B t R x) (@lem6995652 A B t R x)). Qed.
Lemma lem6995660 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term222 A B t R x) = (term285 A B t R x).
Proof. exact (TRANS (@lem6995634 A B t R x) (@lem6995659 A B t R x)). Qed.
Lemma lem6995662 {A : Type'} (x : A) (s : A -> Prop) : (term286 A x s) = (term286 A x s).
Proof. exact (eq_refl (term286 A x s)). Qed.
Lemma lem6995663 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term287 A B s t R x) = (term288 A B s t R x).
Proof. exact (MK_COMB (@lem6995662 A x s) (@lem6995660 A B t R x)). Qed.
Lemma lem6995664 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term223 A B s t R x) = (term287 A B s t R x).
Proof. exact (@lem17265 (@IN A x s) (term222 A B t R x)). Qed.
Lemma lem6995665 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term223 A B s t R x) = (term288 A B s t R x).
Proof. exact (TRANS (@lem6995664 A B s t R x) (@lem6995663 A B s t R x)). Qed.
Lemma lem6995666 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term224 A B s t R) = (term289 A B s t R).
Proof. exact (fun_ext (fun x : A => @lem6995665 A B s t R x)). Qed.
Lemma lem6995667 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6995668 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term34 A B s t R) = (term290 A B s t R).
Proof. exact (MK_COMB (@lem6995667 A) (@lem6995666 A B s t R)). Qed.
Lemma lem6995770 {A : Type'} (P : Prop) (Q : A -> Prop) : (term291 A P Q) = (term292 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem6995771 {B : Type'} (P : Prop) (Q : B -> Prop) : (term291 B P Q) = (term292 B P Q).
Proof. exact (@lem6995770 B P Q). Qed.
Lemma lem6995772 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term293 A B t R x y) = (term294 A B t R x y).
Proof. exact (@lem6995771 B (term228 A B t R x y) (term295 A B t R x y)). Qed.
Lemma lem6995773 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term296 A B t R x y y') = (term269 A B t R x y' y).
Proof. exact (eq_refl (term296 A B t R x y y')). Qed.
Lemma lem6995774 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term230 A B t R x y) = (term230 A B t R x y).
Proof. exact (eq_refl (term230 A B t R x y)). Qed.
Lemma lem6995775 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term297 A B t R x y y') = (term271 A B t R x y' y).
Proof. exact (MK_COMB (@lem6995774 A B t R x y) (@lem6995773 A B t R x y' y)). Qed.
Lemma lem6995776 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term298 A B t R x y) = (term273 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem6995775 A B t R x y' y)). Qed.
Lemma lem6995777 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6995778 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term293 A B t R x y) = (term275 A B t R x y).
Proof. exact (MK_COMB (@lem6995777 B) (@lem6995776 A B t R x y)). Qed.
Lemma lem6995779 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6995780 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term299 A B t R x y) = (term300 A B t R x y).
Proof. exact (MK_COMB (@lem6995779) (@lem6995778 A B t R x y)). Qed.
Lemma lem6995781 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term296 A B t R x y y') = (term269 A B t R x y' y).
Proof. exact (eq_refl (term296 A B t R x y y')). Qed.
Lemma lem6995782 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term301 A B t R x y) = (term295 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem6995781 A B t R x y' y)). Qed.
Lemma lem6995783 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6995784 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term302 A B t R x y) = (term303 A B t R x y).
Proof. exact (MK_COMB (@lem6995783 B) (@lem6995782 A B t R x y)). Qed.
Lemma lem6995785 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term230 A B t R x y) = (term230 A B t R x y).
Proof. exact (eq_refl (term230 A B t R x y)). Qed.
Lemma lem6995786 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term294 A B t R x y) = (term304 A B t R x y).
Proof. exact (MK_COMB (@lem6995785 A B t R x y) (@lem6995784 A B t R x y)). Qed.
Lemma lem6995787 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : ((term293 A B t R x y) = (term294 A B t R x y)) = ((term275 A B t R x y) = (term304 A B t R x y)).
Proof. exact (MK_COMB (@lem6995780 A B t R x y) (@lem6995786 A B t R x y)). Qed.
Lemma lem6995788 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term275 A B t R x y) = (term304 A B t R x y).
Proof. exact (EQ_MP (@lem6995787 A B t R x y) (@lem6995772 A B t R x y)). Qed.
Lemma lem6995837 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term277 A B t R x) = (term305 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem6995788 A B t R x y)). Qed.
Lemma lem6995838 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6995839 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term279 A B t R x) = (term306 A B t R x).
Proof. exact (MK_COMB (@lem6995838 B) (@lem6995837 A B t R x)). Qed.
Lemma lem6995888 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term284 A B t R x) = (term284 A B t R x).
Proof. exact (eq_refl (term284 A B t R x)). Qed.
Lemma lem6995889 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term285 A B t R x) = (term307 A B t R x).
Proof. exact (MK_COMB (@lem6995888 A B t R x) (@lem6995839 A B t R x)). Qed.
Lemma lem6995890 {A : Type'} (x : A) (s : A -> Prop) : (term286 A x s) = (term286 A x s).
Proof. exact (eq_refl (term286 A x s)). Qed.
Lemma lem6995891 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term288 A B s t R x) = (term308 A B s t R x).
Proof. exact (MK_COMB (@lem6995890 A x s) (@lem6995889 A B t R x)). Qed.
Lemma lem6995892 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term289 A B s t R) = (term309 A B s t R).
Proof. exact (fun_ext (fun x : A => @lem6995891 A B s t R x)). Qed.
Lemma lem6995893 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6995894 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term290 A B s t R) = (term310 A B s t R).
Proof. exact (MK_COMB (@lem6995893 A) (@lem6995892 A B s t R)). Qed.
Lemma lem6995944 {A : Type'} (P : A -> Prop) (Q : Prop) : (term311 A P Q) = (term312 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6995945 {B : Type'} (P : B -> Prop) (Q : Prop) : (term311 B P Q) = (term312 B P Q).
Proof. exact (@lem6995944 B P Q). Qed.
Lemma lem6995946 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term313 A B t R x) = (term314 A B t R x).
Proof. exact (@lem6995945 B (term125 A B t R x) (term306 A B t R x)). Qed.
Lemma lem6995947 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term128 A B t R x y) = (term129 A B t R x y).
Proof. exact (eq_refl (term128 A B t R x y)). Qed.
Lemma lem6995948 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term280 A B t R x) = (term125 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem6995947 A B t R x y)). Qed.
Lemma lem6995949 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6995950 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term281 A B t R x) = (term282 A B t R x).
Proof. exact (MK_COMB (@lem6995949 B) (@lem6995948 A B t R x)). Qed.
Lemma lem6995951 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6995952 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term283 A B t R x) = (term284 A B t R x).
Proof. exact (MK_COMB (@lem6995951) (@lem6995950 A B t R x)). Qed.
Lemma lem6995953 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term306 A B t R x) = (term306 A B t R x).
Proof. exact (eq_refl (term306 A B t R x)). Qed.
Lemma lem6995954 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term313 A B t R x) = (term307 A B t R x).
Proof. exact (MK_COMB (@lem6995952 A B t R x) (@lem6995953 A B t R x)). Qed.
Lemma lem6995955 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6995956 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term315 A B t R x) = (term316 A B t R x).
Proof. exact (MK_COMB (@lem6995955) (@lem6995954 A B t R x)). Qed.
Lemma lem6995957 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term128 A B t R x y) = (term129 A B t R x y).
Proof. exact (eq_refl (term128 A B t R x y)). Qed.
Lemma lem6995958 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6995959 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term317 A B t R x y) = (term318 A B t R x y).
Proof. exact (MK_COMB (@lem6995958) (@lem6995957 A B t R x y)). Qed.
Lemma lem6995960 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term306 A B t R x) = (term306 A B t R x).
Proof. exact (eq_refl (term306 A B t R x)). Qed.
Lemma lem6995961 {A B : Type'} (y : B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term319 A B y t R x) = (term320 A B y t R x).
Proof. exact (MK_COMB (@lem6995959 A B t R x y) (@lem6995960 A B t R x)). Qed.
Lemma lem6995962 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term321 A B t R x) = (term322 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem6995961 A B y t R x)). Qed.
Lemma lem6995963 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6995964 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term314 A B t R x) = (term323 A B t R x).
Proof. exact (MK_COMB (@lem6995963 B) (@lem6995962 A B t R x)). Qed.
Lemma lem6995965 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : ((term313 A B t R x) = (term314 A B t R x)) = ((term307 A B t R x) = (term323 A B t R x)).
Proof. exact (MK_COMB (@lem6995956 A B t R x) (@lem6995964 A B t R x)). Qed.
Lemma lem6995966 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term307 A B t R x) = (term323 A B t R x).
Proof. exact (EQ_MP (@lem6995965 A B t R x) (@lem6995946 A B t R x)). Qed.
Lemma lem6995967 {A : Type'} (x : A) (s : A -> Prop) : (term286 A x s) = (term286 A x s).
Proof. exact (eq_refl (term286 A x s)). Qed.
Lemma lem6995968 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term308 A B s t R x) = (term324 A B s t R x).
Proof. exact (MK_COMB (@lem6995967 A x s) (@lem6995966 A B t R x)). Qed.
Lemma lem6995970 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6995971 {B : Type'} (P : Prop) (Q : B -> Prop) : (term325 B P Q) = (term326 B P Q).
Proof. exact (@lem6995970 B P Q). Qed.
Lemma lem6995972 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term327 A B s t R x) = (term328 A B s t R x).
Proof. exact (@lem6995971 B (term329 A x s) (term322 A B t R x)). Qed.
Lemma lem6995973 {A B : Type'} (y : B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term330 A B t R x y) = (term320 A B y t R x).
Proof. exact (eq_refl (term330 A B t R x y)). Qed.
Lemma lem6995974 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term331 A B t R x) = (term322 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem6995973 A B y t R x)). Qed.
Lemma lem6995975 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6995976 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term332 A B t R x) = (term323 A B t R x).
Proof. exact (MK_COMB (@lem6995975 B) (@lem6995974 A B t R x)). Qed.
Lemma lem6995977 {A : Type'} (x : A) (s : A -> Prop) : (term286 A x s) = (term286 A x s).
Proof. exact (eq_refl (term286 A x s)). Qed.
Lemma lem6995978 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term327 A B s t R x) = (term324 A B s t R x).
Proof. exact (MK_COMB (@lem6995977 A x s) (@lem6995976 A B t R x)). Qed.
Lemma lem6995979 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6995980 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term333 A B s t R x) = (term334 A B s t R x).
Proof. exact (MK_COMB (@lem6995979) (@lem6995978 A B s t R x)). Qed.
Lemma lem6995981 {A B : Type'} (y : B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term330 A B t R x y) = (term320 A B y t R x).
Proof. exact (eq_refl (term330 A B t R x y)). Qed.
Lemma lem6995982 {A : Type'} (x : A) (s : A -> Prop) : (term286 A x s) = (term286 A x s).
Proof. exact (eq_refl (term286 A x s)). Qed.
Lemma lem6995983 {A B : Type'} (s : A -> Prop) (y : B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term335 A B s t R x y) = (term336 A B s y t R x).
Proof. exact (MK_COMB (@lem6995982 A x s) (@lem6995981 A B y t R x)). Qed.
Lemma lem6995984 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term337 A B s t R x) = (term338 A B s t R x).
Proof. exact (fun_ext (fun y : B => @lem6995983 A B s y t R x)). Qed.
Lemma lem6995985 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6995986 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term328 A B s t R x) = (term339 A B s t R x).
Proof. exact (MK_COMB (@lem6995985 B) (@lem6995984 A B s t R x)). Qed.
Lemma lem6995987 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : ((term327 A B s t R x) = (term328 A B s t R x)) = ((term324 A B s t R x) = (term339 A B s t R x)).
Proof. exact (MK_COMB (@lem6995980 A B s t R x) (@lem6995986 A B s t R x)). Qed.
Lemma lem6995988 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term324 A B s t R x) = (term339 A B s t R x).
Proof. exact (EQ_MP (@lem6995987 A B s t R x) (@lem6995972 A B s t R x)). Qed.
Lemma lem6995989 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term308 A B s t R x) = (term339 A B s t R x).
Proof. exact (TRANS (@lem6995968 A B s t R x) (@lem6995988 A B s t R x)). Qed.
Lemma lem6995990 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term309 A B s t R) = (term340 A B s t R).
Proof. exact (fun_ext (fun x : A => @lem6995989 A B s t R x)). Qed.
Lemma lem6995991 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6995992 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term310 A B s t R) = (term341 A B s t R).
Proof. exact (MK_COMB (@lem6995991 A) (@lem6995990 A B s t R)). Qed.
Lemma lem6995994 {A B : Type'} (P : type1413 A B) : (term342 A B P) = (term343 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6995995 {A B : Type'} (P : type1413 A B) : (term342 A B P) = (term343 A B P).
Proof. exact (@lem6995994 A B P). Qed.
Lemma lem6995996 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term344 A B s t R) = (term345 A B s t R).
Proof. exact (@lem6995995 A B (term346 A B s t R)). Qed.
Lemma lem6995997 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term347 A B s t R x) = (term338 A B s t R x).
Proof. exact (eq_refl (term347 A B s t R x)). Qed.
Lemma lem6995998 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6995999 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term348 A B s t R x y) = (term349 A B s t R x y).
Proof. exact (MK_COMB (@lem6995997 A B s t R x) (@lem6995998 B y)). Qed.
Lemma lem6996000 {A B : Type'} (s : A -> Prop) (y : B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term349 A B s t R x y) = (term336 A B s y t R x).
Proof. exact (eq_refl (term349 A B s t R x y)). Qed.
Lemma lem6996001 {A B : Type'} (s : A -> Prop) (y : B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term348 A B s t R x y) = (term336 A B s y t R x).
Proof. exact (TRANS (@lem6995999 A B s t R x y) (@lem6996000 A B s y t R x)). Qed.
Lemma lem6996002 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term350 A B s t R x) = (term338 A B s t R x).
Proof. exact (fun_ext (fun y : B => @lem6996001 A B s y t R x)). Qed.
Lemma lem6996003 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6996004 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term351 A B s t R x) = (term339 A B s t R x).
Proof. exact (MK_COMB (@lem6996003 B) (@lem6996002 A B s t R x)). Qed.
Lemma lem6996005 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term352 A B s t R) = (term340 A B s t R).
Proof. exact (fun_ext (fun x : A => @lem6996004 A B s t R x)). Qed.
Lemma lem6996006 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6996007 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term344 A B s t R) = (term341 A B s t R).
Proof. exact (MK_COMB (@lem6996006 A) (@lem6996005 A B s t R)). Qed.
Lemma lem6996008 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6996009 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term353 A B s t R) = (term354 A B s t R).
Proof. exact (MK_COMB (@lem6996008) (@lem6996007 A B s t R)). Qed.
Lemma lem6996010 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term347 A B s t R x) = (term338 A B s t R x).
Proof. exact (eq_refl (term347 A B s t R x)). Qed.
Lemma lem6996011 {A B : Type'} (y : A -> B) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem6996012 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term355 A B s t R y x) = (term356 A B s t R y x).
Proof. exact (MK_COMB (@lem6996010 A B s t R x) (@lem6996011 A B y x)). Qed.
Lemma lem6996013 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term356 A B s t R y x) = (term357 A B s y t R x).
Proof. exact (eq_refl (term356 A B s t R y x)). Qed.
Lemma lem6996014 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term355 A B s t R y x) = (term357 A B s y t R x).
Proof. exact (TRANS (@lem6996012 A B s t R y x) (@lem6996013 A B s y t R x)). Qed.
Lemma lem6996015 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term358 A B s t R y) = (term359 A B s y t R).
Proof. exact (fun_ext (fun x : A => @lem6996014 A B s y t R x)). Qed.
Lemma lem6996016 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6996017 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term360 A B s t R y) = (term361 A B s y t R).
Proof. exact (MK_COMB (@lem6996016 A) (@lem6996015 A B s y t R)). Qed.
Lemma lem6996018 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term362 A B s t R) = (term363 A B s t R).
Proof. exact (fun_ext (fun y : A -> B => @lem6996017 A B s y t R)). Qed.
Lemma lem6996019 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem6996020 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term345 A B s t R) = (term364 A B s t R).
Proof. exact (MK_COMB (@lem6996019 A B) (@lem6996018 A B s t R)). Qed.
Lemma lem6996021 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : ((term344 A B s t R) = (term345 A B s t R)) = ((term341 A B s t R) = (term364 A B s t R)).
Proof. exact (MK_COMB (@lem6996009 A B s t R) (@lem6996020 A B s t R)). Qed.
Lemma lem6996022 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term341 A B s t R) = (term364 A B s t R).
Proof. exact (EQ_MP (@lem6996021 A B s t R) (@lem6995996 A B s t R)). Qed.
Lemma lem6996023 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term310 A B s t R) = (term364 A B s t R).
Proof. exact (TRANS (@lem6995992 A B s t R) (@lem6996022 A B s t R)). Qed.
Lemma lem6996024 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term290 A B s t R) = (term364 A B s t R).
Proof. exact (TRANS (@lem6995894 A B s t R) (@lem6996023 A B s t R)). Qed.
Lemma lem6996025 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term34 A B s t R) = (term364 A B s t R).
Proof. exact (TRANS (@lem6995668 A B s t R) (@lem6996024 A B s t R)). Qed.
Lemma lem6996026 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (h1 : term34 A B s t R) : term364 A B s t R.
Proof. exact (EQ_MP (@lem6996025 A B s t R) (@lem6995400 A B s t R h1)). Qed.
Lemma lem6996032 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem6996038 {A B : Type'} (_93258 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) (h1 : term226 A B _93258 R x t) : term226 A B _93258 R x t.
Proof. exact (h1). Qed.
Lemma lem6996039 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term361 A B s y t R.
Proof. exact (h1). Qed.
Lemma lem6996050 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996051 {A B : Type'} (f : type830 A B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) f x).
Proof. exact (@lem6996050 (B -> Prop) (type467 A B) f x). Qed.
Lemma lem6996052 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) : (_93258 t) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _93258 t).
Proof. exact (@lem6996051 A B _93258 t). Qed.
Lemma lem6996053 {A B : Type'} (R : type1413 A B) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem6996054 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (_93258 t R) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _93258 t R).
Proof. exact (MK_COMB (@lem6996052 A B _93258 t) (@lem6996053 A B R)). Qed.
Lemma lem6996056 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996057 {A B : Type'} (f : type467 A B) (x : type1413 A B) : (f x) = (@I ((A -> B -> Prop) -> A -> B) f x).
Proof. exact (@lem6996056 (type1413 A B) (A -> B) f x). Qed.
Lemma lem6996058 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _93258 t R) = (term365 A B _93258 t R).
Proof. exact (@lem6996057 A B (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _93258 t) R). Qed.
Lemma lem6996059 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (_93258 t R) = (term365 A B _93258 t R).
Proof. exact (TRANS (@lem6996054 A B _93258 t R) (@lem6996058 A B _93258 t R)). Qed.
Lemma lem6996060 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6996061 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (_93258 t R x) = (term366 A B _93258 t R x).
Proof. exact (MK_COMB (@lem6996059 A B _93258 t R) (@lem6996060 A x)). Qed.
Lemma lem6996063 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996064 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6996063 A B f x). Qed.
Lemma lem6996065 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term366 A B _93258 t R x) = (term367 A B _93258 t R x).
Proof. exact (@lem6996064 A B (term365 A B _93258 t R) x). Qed.
Lemma lem6996067 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (_93258 t R x) = (term367 A B _93258 t R x).
Proof. exact (TRANS (@lem6996061 A B _93258 t R x) (@lem6996065 A B _93258 t R x)). Qed.
Lemma lem6996068 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (R x).
Proof. exact (eq_refl (R x)). Qed.
Lemma lem6996069 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term161 A B _93258 t R x) = (term368 A B _93258 t R x).
Proof. exact (MK_COMB (@lem6996068 A B R x) (@lem6996067 A B _93258 t R x)). Qed.
Lemma lem6996071 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996072 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem6996071 A (B -> Prop) f x). Qed.
Lemma lem6996073 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (@I (A -> B -> Prop) R x).
Proof. exact (@lem6996072 A B R x). Qed.
Lemma lem6996074 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term367 A B _93258 t R x) = (term367 A B _93258 t R x).
Proof. exact (eq_refl (term367 A B _93258 t R x)). Qed.
Lemma lem6996075 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term368 A B _93258 t R x) = (term369 A B _93258 t R x).
Proof. exact (MK_COMB (@lem6996073 A B R x) (@lem6996074 A B _93258 t R x)). Qed.
Lemma lem6996077 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996078 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem6996077 B Prop f x). Qed.
Lemma lem6996079 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term369 A B _93258 t R x) = (term370 A B _93258 t R x).
Proof. exact (@lem6996078 B (@I (A -> B -> Prop) R x) (term367 A B _93258 t R x)). Qed.
Lemma lem6996080 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term368 A B _93258 t R x) = (term370 A B _93258 t R x).
Proof. exact (TRANS (@lem6996075 A B _93258 t R x) (@lem6996079 A B _93258 t R x)). Qed.
Lemma lem6996081 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term161 A B _93258 t R x) = (term370 A B _93258 t R x).
Proof. exact (TRANS (@lem6996069 A B _93258 t R x) (@lem6996080 A B _93258 t R x)). Qed.
Lemma lem6996082 {B : Type'} : (@IN B) = (@IN B).
Proof. exact (eq_refl (@IN B)). Qed.
Lemma lem6996091 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996092 {A B : Type'} (f : type830 A B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) f x).
Proof. exact (@lem6996091 (B -> Prop) (type467 A B) f x). Qed.
Lemma lem6996093 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) : (_93258 t) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _93258 t).
Proof. exact (@lem6996092 A B _93258 t). Qed.
Lemma lem6996094 {A B : Type'} (R : type1413 A B) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem6996095 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (_93258 t R) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _93258 t R).
Proof. exact (MK_COMB (@lem6996093 A B _93258 t) (@lem6996094 A B R)). Qed.
Lemma lem6996097 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996098 {A B : Type'} (f : type467 A B) (x : type1413 A B) : (f x) = (@I ((A -> B -> Prop) -> A -> B) f x).
Proof. exact (@lem6996097 (type1413 A B) (A -> B) f x). Qed.
Lemma lem6996099 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _93258 t R) = (term365 A B _93258 t R).
Proof. exact (@lem6996098 A B (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _93258 t) R). Qed.
Lemma lem6996100 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (_93258 t R) = (term365 A B _93258 t R).
Proof. exact (TRANS (@lem6996095 A B _93258 t R) (@lem6996099 A B _93258 t R)). Qed.
Lemma lem6996101 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6996102 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (_93258 t R x) = (term366 A B _93258 t R x).
Proof. exact (MK_COMB (@lem6996100 A B _93258 t R) (@lem6996101 A x)). Qed.
Lemma lem6996104 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996105 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6996104 A B f x). Qed.
Lemma lem6996106 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term366 A B _93258 t R x) = (term367 A B _93258 t R x).
Proof. exact (@lem6996105 A B (term365 A B _93258 t R) x). Qed.
Lemma lem6996108 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (_93258 t R x) = (term367 A B _93258 t R x).
Proof. exact (TRANS (@lem6996102 A B _93258 t R x) (@lem6996106 A B _93258 t R x)). Qed.
Lemma lem6996109 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem6996110 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term156 A B _93258 t R x) = (term371 A B _93258 t R x).
Proof. exact (MK_COMB (@lem6996082 B) (@lem6996108 A B _93258 t R x)). Qed.
Lemma lem6996111 {A B : Type'} (_93258 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term157 A B _93258 R x t) = (term372 A B _93258 R x t).
Proof. exact (MK_COMB (@lem6996110 A B _93258 t R x) (@lem6996109 B t)). Qed.
Lemma lem6996113 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996114 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem6996113 B (type686 B) f x). Qed.
Lemma lem6996115 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term371 A B _93258 t R x) = (term373 A B _93258 t R x).
Proof. exact (@lem6996114 B (@IN B) (term367 A B _93258 t R x)). Qed.
Lemma lem6996116 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem6996117 {A B : Type'} (_93258 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term372 A B _93258 R x t) = (term374 A B _93258 R x t).
Proof. exact (MK_COMB (@lem6996115 A B _93258 t R x) (@lem6996116 B t)). Qed.
Lemma lem6996119 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996120 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem6996119 (B -> Prop) Prop f x). Qed.
Lemma lem6996121 {A B : Type'} (_93258 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term374 A B _93258 R x t) = (term375 A B _93258 R x t).
Proof. exact (@lem6996120 B (term373 A B _93258 t R x) t). Qed.
Lemma lem6996122 {A B : Type'} (_93258 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term372 A B _93258 R x t) = (term375 A B _93258 R x t).
Proof. exact (TRANS (@lem6996117 A B _93258 R x t) (@lem6996121 A B _93258 R x t)). Qed.
Lemma lem6996123 {A B : Type'} (_93258 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term157 A B _93258 R x t) = (term375 A B _93258 R x t).
Proof. exact (TRANS (@lem6996111 A B _93258 R x t) (@lem6996122 A B _93258 R x t)). Qed.
Lemma lem6996124 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6996125 {A B : Type'} (_93258 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term159 A B _93258 R x t) = (term376 A B _93258 R x t).
Proof. exact (MK_COMB (@lem6996124) (@lem6996123 A B _93258 R x t)). Qed.
Lemma lem6996126 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term162 A B _93258 t R x) = (term377 A B _93258 t R x).
Proof. exact (MK_COMB (@lem6996125 A B _93258 R x t) (@lem6996081 A B _93258 t R x)). Qed.
Lemma lem6996127 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6996134 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996135 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem6996134 A (B -> Prop) f x). Qed.
Lemma lem6996136 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (@I (A -> B -> Prop) R x).
Proof. exact (@lem6996135 A B R x). Qed.
Lemma lem6996137 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6996138 {A B : Type'} (R : type1413 A B) (x : A) (x' : B) : (R x x') = (@I (A -> B -> Prop) R x x').
Proof. exact (MK_COMB (@lem6996136 A B R x) (@lem6996137 B x')). Qed.
Lemma lem6996140 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996141 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem6996140 B Prop f x). Qed.
Lemma lem6996142 {A B : Type'} (R : type1413 A B) (x : A) (x' : B) : (@I (A -> B -> Prop) R x x') = (term378 A B R x x').
Proof. exact (@lem6996141 B (@I (A -> B -> Prop) R x) x'). Qed.
Lemma lem6996144 {A B : Type'} (R : type1413 A B) (x : A) (x' : B) : (R x x') = (term378 A B R x x').
Proof. exact (TRANS (@lem6996138 A B R x x') (@lem6996142 A B R x x')). Qed.
Lemma lem6996145 {A B : Type'} (R : type1413 A B) (x : A) (x' : B) : (term379 A B R x x') = (term380 A B R x x').
Proof. exact (MK_COMB (@lem6996127) (@lem6996144 A B R x x')). Qed.
Lemma lem6996146 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6996153 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996154 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem6996153 B (type686 B) f x). Qed.
Lemma lem6996155 {B : Type'} (x : B) : (@IN B x) = (@I (B -> (B -> Prop) -> Prop) (@IN B) x).
Proof. exact (@lem6996154 B (@IN B) x). Qed.
Lemma lem6996156 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem6996157 {B : Type'} (x : B) (t : B -> Prop) : (@IN B x t) = (@I (B -> (B -> Prop) -> Prop) (@IN B) x t).
Proof. exact (MK_COMB (@lem6996155 B x) (@lem6996156 B t)). Qed.
Lemma lem6996159 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996160 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem6996159 (B -> Prop) Prop f x). Qed.
Lemma lem6996161 {B : Type'} (x : B) (t : B -> Prop) : (@I (B -> (B -> Prop) -> Prop) (@IN B) x t) = (term381 B x t).
Proof. exact (@lem6996160 B (@I (B -> (B -> Prop) -> Prop) (@IN B) x) t). Qed.
Lemma lem6996163 {B : Type'} (x : B) (t : B -> Prop) : (@IN B x t) = (term381 B x t).
Proof. exact (TRANS (@lem6996157 B x t) (@lem6996161 B x t)). Qed.
Lemma lem6996164 {B : Type'} (x : B) (t : B -> Prop) : (term329 B x t) = (term382 B x t).
Proof. exact (MK_COMB (@lem6996146) (@lem6996163 B x t)). Qed.
Lemma lem6996165 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6996166 {B : Type'} (x : B) (t : B -> Prop) : (term286 B x t) = (term383 B x t).
Proof. exact (MK_COMB (@lem6996165) (@lem6996164 B x t)). Qed.
Lemma lem6996167 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term228 A B t R x x') = (term384 A B t R x x').
Proof. exact (MK_COMB (@lem6996166 B x' t) (@lem6996145 A B R x x')). Qed.
Lemma lem6996168 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term245 A B t R x) = (term385 A B t R x).
Proof. exact (fun_ext (fun x' : B => @lem6996167 A B t R x x')). Qed.
Lemma lem6996169 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6996170 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term254 A B t R x) = (term386 A B t R x).
Proof. exact (MK_COMB (@lem6996169 B) (@lem6996168 A B t R x)). Qed.
Lemma lem6996171 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6996172 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term256 A B t R x) = (term387 A B t R x).
Proof. exact (MK_COMB (@lem6996171) (@lem6996170 A B t R x)). Qed.
Lemma lem6996173 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term257 A B _93258 t R x) = (term388 A B _93258 t R x).
Proof. exact (MK_COMB (@lem6996172 A B t R x) (@lem6996126 A B _93258 t R x)). Qed.
Lemma lem6996174 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term258 A B _93258 t R) = (term389 A B _93258 t R).
Proof. exact (fun_ext (fun x : A => @lem6996173 A B _93258 t R x)). Qed.
Lemma lem6996175 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6996176 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term259 A B _93258 t R) = (term390 A B _93258 t R).
Proof. exact (MK_COMB (@lem6996175 A) (@lem6996174 A B _93258 t R)). Qed.
Lemma lem6996177 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) : (term260 A B _93258 t) = (term391 A B _93258 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem6996176 A B _93258 t R)). Qed.
Lemma lem6996178 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem6996179 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) : (term261 A B _93258 t) = (term392 A B _93258 t).
Proof. exact (MK_COMB (@lem6996178 A B) (@lem6996177 A B _93258 t)). Qed.
Lemma lem6996180 {A B : Type'} (_93258 : type830 A B) : (term262 A B _93258) = (term393 A B _93258).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6996179 A B _93258 t)). Qed.
Lemma lem6996181 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6996182 {A B : Type'} (_93258 : type830 A B) : (term263 A B _93258) = (term394 A B _93258).
Proof. exact (MK_COMB (@lem6996181 B) (@lem6996180 A B _93258)). Qed.
Lemma lem6996183 {A B : Type'} (_93258 : type830 A B) (h1 : term174 A B _93258) : term394 A B _93258.
Proof. exact (EQ_MP (@lem6996182 A B _93258) (@lem6995608 A B _93258 h1)). Qed.
Lemma lem6996199 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996200 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6996199 A (type686 A) f x). Qed.
Lemma lem6996201 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem6996200 A (@IN A) x). Qed.
Lemma lem6996202 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6996203 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem6996201 A x) (@lem6996202 A s)). Qed.
Lemma lem6996205 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996206 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6996205 (A -> Prop) Prop f x). Qed.
Lemma lem6996207 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term381 A x s).
Proof. exact (@lem6996206 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem6996209 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term381 A x s).
Proof. exact (TRANS (@lem6996203 A x s) (@lem6996207 A x s)). Qed.
Lemma lem6996211 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6996212 {B : Type'} : (@IN B) = (@IN B).
Proof. exact (eq_refl (@IN B)). Qed.
Lemma lem6996221 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996222 {A B : Type'} (f : type830 A B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) f x).
Proof. exact (@lem6996221 (B -> Prop) (type467 A B) f x). Qed.
Lemma lem6996223 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) : (_93258 t) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _93258 t).
Proof. exact (@lem6996222 A B _93258 t). Qed.
Lemma lem6996224 {A B : Type'} (R : type1413 A B) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem6996225 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (_93258 t R) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _93258 t R).
Proof. exact (MK_COMB (@lem6996223 A B _93258 t) (@lem6996224 A B R)). Qed.
Lemma lem6996227 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996228 {A B : Type'} (f : type467 A B) (x : type1413 A B) : (f x) = (@I ((A -> B -> Prop) -> A -> B) f x).
Proof. exact (@lem6996227 (type1413 A B) (A -> B) f x). Qed.
Lemma lem6996229 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _93258 t R) = (term365 A B _93258 t R).
Proof. exact (@lem6996228 A B (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _93258 t) R). Qed.
Lemma lem6996230 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (_93258 t R) = (term365 A B _93258 t R).
Proof. exact (TRANS (@lem6996225 A B _93258 t R) (@lem6996229 A B _93258 t R)). Qed.
Lemma lem6996231 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6996232 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (_93258 t R x) = (term366 A B _93258 t R x).
Proof. exact (MK_COMB (@lem6996230 A B _93258 t R) (@lem6996231 A x)). Qed.
Lemma lem6996234 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996235 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6996234 A B f x). Qed.
Lemma lem6996236 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term366 A B _93258 t R x) = (term367 A B _93258 t R x).
Proof. exact (@lem6996235 A B (term365 A B _93258 t R) x). Qed.
Lemma lem6996238 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (_93258 t R x) = (term367 A B _93258 t R x).
Proof. exact (TRANS (@lem6996232 A B _93258 t R x) (@lem6996236 A B _93258 t R x)). Qed.
Lemma lem6996239 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem6996240 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term156 A B _93258 t R x) = (term371 A B _93258 t R x).
Proof. exact (MK_COMB (@lem6996212 B) (@lem6996238 A B _93258 t R x)). Qed.
Lemma lem6996241 {A B : Type'} (_93258 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term157 A B _93258 R x t) = (term372 A B _93258 R x t).
Proof. exact (MK_COMB (@lem6996240 A B _93258 t R x) (@lem6996239 B t)). Qed.
Lemma lem6996243 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996244 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem6996243 B (type686 B) f x). Qed.
Lemma lem6996245 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term371 A B _93258 t R x) = (term373 A B _93258 t R x).
Proof. exact (@lem6996244 B (@IN B) (term367 A B _93258 t R x)). Qed.
Lemma lem6996246 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem6996247 {A B : Type'} (_93258 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term372 A B _93258 R x t) = (term374 A B _93258 R x t).
Proof. exact (MK_COMB (@lem6996245 A B _93258 t R x) (@lem6996246 B t)). Qed.
Lemma lem6996249 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996250 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem6996249 (B -> Prop) Prop f x). Qed.
Lemma lem6996251 {A B : Type'} (_93258 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term374 A B _93258 R x t) = (term375 A B _93258 R x t).
Proof. exact (@lem6996250 B (term373 A B _93258 t R x) t). Qed.
Lemma lem6996252 {A B : Type'} (_93258 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term372 A B _93258 R x t) = (term375 A B _93258 R x t).
Proof. exact (TRANS (@lem6996247 A B _93258 R x t) (@lem6996251 A B _93258 R x t)). Qed.
Lemma lem6996253 {A B : Type'} (_93258 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term157 A B _93258 R x t) = (term375 A B _93258 R x t).
Proof. exact (TRANS (@lem6996241 A B _93258 R x t) (@lem6996252 A B _93258 R x t)). Qed.
Lemma lem6996254 {A B : Type'} (_93258 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term226 A B _93258 R x t) = (term395 A B _93258 R x t).
Proof. exact (MK_COMB (@lem6996211) (@lem6996253 A B _93258 R x t)). Qed.
Lemma lem6996260 {B : Type'} (y' : B) (y : B) : (y' = y) = (y' = y).
Proof. exact (eq_refl (y' = y)). Qed.
Lemma lem6996261 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6996268 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996269 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem6996268 A (B -> Prop) f x). Qed.
Lemma lem6996270 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (@I (A -> B -> Prop) R x).
Proof. exact (@lem6996269 A B R x). Qed.
Lemma lem6996271 {B : Type'} (y' : B) : y' = y'.
Proof. exact (eq_refl y'). Qed.
Lemma lem6996272 {A B : Type'} (R : type1413 A B) (x : A) (y' : B) : (R x y') = (@I (A -> B -> Prop) R x y').
Proof. exact (MK_COMB (@lem6996270 A B R x) (@lem6996271 B y')). Qed.
Lemma lem6996274 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996275 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem6996274 B Prop f x). Qed.
Lemma lem6996276 {A B : Type'} (R : type1413 A B) (x : A) (y' : B) : (@I (A -> B -> Prop) R x y') = (term378 A B R x y').
Proof. exact (@lem6996275 B (@I (A -> B -> Prop) R x) y'). Qed.
Lemma lem6996278 {A B : Type'} (R : type1413 A B) (x : A) (y' : B) : (R x y') = (term378 A B R x y').
Proof. exact (TRANS (@lem6996272 A B R x y') (@lem6996276 A B R x y')). Qed.
Lemma lem6996279 {A B : Type'} (R : type1413 A B) (x : A) (y' : B) : (term379 A B R x y') = (term380 A B R x y').
Proof. exact (MK_COMB (@lem6996261) (@lem6996278 A B R x y')). Qed.
Lemma lem6996280 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6996287 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996288 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem6996287 B (type686 B) f x). Qed.
Lemma lem6996289 {B : Type'} (y' : B) : (@IN B y') = (@I (B -> (B -> Prop) -> Prop) (@IN B) y').
Proof. exact (@lem6996288 B (@IN B) y'). Qed.
Lemma lem6996290 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem6996291 {B : Type'} (y' : B) (t : B -> Prop) : (@IN B y' t) = (@I (B -> (B -> Prop) -> Prop) (@IN B) y' t).
Proof. exact (MK_COMB (@lem6996289 B y') (@lem6996290 B t)). Qed.
Lemma lem6996293 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996294 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem6996293 (B -> Prop) Prop f x). Qed.
Lemma lem6996295 {B : Type'} (y' : B) (t : B -> Prop) : (@I (B -> (B -> Prop) -> Prop) (@IN B) y' t) = (term381 B y' t).
Proof. exact (@lem6996294 B (@I (B -> (B -> Prop) -> Prop) (@IN B) y') t). Qed.
Lemma lem6996297 {B : Type'} (y' : B) (t : B -> Prop) : (@IN B y' t) = (term381 B y' t).
Proof. exact (TRANS (@lem6996291 B y' t) (@lem6996295 B y' t)). Qed.
Lemma lem6996298 {B : Type'} (y' : B) (t : B -> Prop) : (term329 B y' t) = (term382 B y' t).
Proof. exact (MK_COMB (@lem6996280) (@lem6996297 B y' t)). Qed.
Lemma lem6996299 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6996300 {B : Type'} (y' : B) (t : B -> Prop) : (term286 B y' t) = (term383 B y' t).
Proof. exact (MK_COMB (@lem6996299) (@lem6996298 B y' t)). Qed.
Lemma lem6996301 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term228 A B t R x y') = (term384 A B t R x y').
Proof. exact (MK_COMB (@lem6996300 B y' t) (@lem6996279 A B R x y')). Qed.
Lemma lem6996302 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6996303 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term230 A B t R x y') = (term396 A B t R x y').
Proof. exact (MK_COMB (@lem6996302) (@lem6996301 A B t R x y')). Qed.
Lemma lem6996304 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term269 A B t R x y' y) = (term397 A B t R x y' y).
Proof. exact (MK_COMB (@lem6996303 A B t R x y') (@lem6996260 B y' y)). Qed.
Lemma lem6996305 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term295 A B t R x y) = (term398 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem6996304 A B t R x y' y)). Qed.
Lemma lem6996306 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6996307 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term303 A B t R x y) = (term399 A B t R x y).
Proof. exact (MK_COMB (@lem6996306 B) (@lem6996305 A B t R x y)). Qed.
Lemma lem6996308 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6996315 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996316 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem6996315 A (B -> Prop) f x). Qed.
Lemma lem6996317 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (@I (A -> B -> Prop) R x).
Proof. exact (@lem6996316 A B R x). Qed.
Lemma lem6996318 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6996319 {A B : Type'} (R : type1413 A B) (x : A) (y : B) : (R x y) = (@I (A -> B -> Prop) R x y).
Proof. exact (MK_COMB (@lem6996317 A B R x) (@lem6996318 B y)). Qed.
Lemma lem6996321 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996322 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem6996321 B Prop f x). Qed.
Lemma lem6996323 {A B : Type'} (R : type1413 A B) (x : A) (y : B) : (@I (A -> B -> Prop) R x y) = (term378 A B R x y).
Proof. exact (@lem6996322 B (@I (A -> B -> Prop) R x) y). Qed.
Lemma lem6996325 {A B : Type'} (R : type1413 A B) (x : A) (y : B) : (R x y) = (term378 A B R x y).
Proof. exact (TRANS (@lem6996319 A B R x y) (@lem6996323 A B R x y)). Qed.
Lemma lem6996326 {A B : Type'} (R : type1413 A B) (x : A) (y : B) : (term379 A B R x y) = (term380 A B R x y).
Proof. exact (MK_COMB (@lem6996308) (@lem6996325 A B R x y)). Qed.
Lemma lem6996327 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6996334 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996335 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem6996334 B (type686 B) f x). Qed.
Lemma lem6996336 {B : Type'} (y : B) : (@IN B y) = (@I (B -> (B -> Prop) -> Prop) (@IN B) y).
Proof. exact (@lem6996335 B (@IN B) y). Qed.
Lemma lem6996337 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem6996338 {B : Type'} (y : B) (t : B -> Prop) : (@IN B y t) = (@I (B -> (B -> Prop) -> Prop) (@IN B) y t).
Proof. exact (MK_COMB (@lem6996336 B y) (@lem6996337 B t)). Qed.
Lemma lem6996340 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996341 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem6996340 (B -> Prop) Prop f x). Qed.
Lemma lem6996342 {B : Type'} (y : B) (t : B -> Prop) : (@I (B -> (B -> Prop) -> Prop) (@IN B) y t) = (term381 B y t).
Proof. exact (@lem6996341 B (@I (B -> (B -> Prop) -> Prop) (@IN B) y) t). Qed.
Lemma lem6996344 {B : Type'} (y : B) (t : B -> Prop) : (@IN B y t) = (term381 B y t).
Proof. exact (TRANS (@lem6996338 B y t) (@lem6996342 B y t)). Qed.
Lemma lem6996345 {B : Type'} (y : B) (t : B -> Prop) : (term329 B y t) = (term382 B y t).
Proof. exact (MK_COMB (@lem6996327) (@lem6996344 B y t)). Qed.
Lemma lem6996346 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6996347 {B : Type'} (y : B) (t : B -> Prop) : (term286 B y t) = (term383 B y t).
Proof. exact (MK_COMB (@lem6996346) (@lem6996345 B y t)). Qed.
Lemma lem6996348 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term228 A B t R x y) = (term384 A B t R x y).
Proof. exact (MK_COMB (@lem6996347 B y t) (@lem6996326 A B R x y)). Qed.
Lemma lem6996349 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6996350 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term230 A B t R x y) = (term396 A B t R x y).
Proof. exact (MK_COMB (@lem6996349) (@lem6996348 A B t R x y)). Qed.
Lemma lem6996351 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term304 A B t R x y) = (term400 A B t R x y).
Proof. exact (MK_COMB (@lem6996350 A B t R x y) (@lem6996307 A B t R x y)). Qed.
Lemma lem6996352 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term305 A B t R x) = (term401 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem6996351 A B t R x y)). Qed.
Lemma lem6996353 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6996354 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term306 A B t R x) = (term402 A B t R x).
Proof. exact (MK_COMB (@lem6996353 B) (@lem6996352 A B t R x)). Qed.
Lemma lem6996361 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996362 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6996361 A B f x). Qed.
Lemma lem6996364 {A B : Type'} (y : A -> B) (x : A) : (y x) = (@I (A -> B) y x).
Proof. exact (@lem6996362 A B y x). Qed.
Lemma lem6996365 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (R x).
Proof. exact (eq_refl (R x)). Qed.
Lemma lem6996366 {A B : Type'} (R : type1413 A B) (y : A -> B) (x : A) : (term403 A B R y x) = (term404 A B R y x).
Proof. exact (MK_COMB (@lem6996365 A B R x) (@lem6996364 A B y x)). Qed.
Lemma lem6996368 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996369 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem6996368 A (B -> Prop) f x). Qed.
Lemma lem6996370 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (@I (A -> B -> Prop) R x).
Proof. exact (@lem6996369 A B R x). Qed.
Lemma lem6996371 {A B : Type'} (y : A -> B) (x : A) : (@I (A -> B) y x) = (@I (A -> B) y x).
Proof. exact (eq_refl (@I (A -> B) y x)). Qed.
Lemma lem6996372 {A B : Type'} (R : type1413 A B) (y : A -> B) (x : A) : (term404 A B R y x) = (term405 A B R y x).
Proof. exact (MK_COMB (@lem6996370 A B R x) (@lem6996371 A B y x)). Qed.
Lemma lem6996374 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996375 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem6996374 B Prop f x). Qed.
Lemma lem6996376 {A B : Type'} (R : type1413 A B) (y : A -> B) (x : A) : (term405 A B R y x) = (term406 A B R y x).
Proof. exact (@lem6996375 B (@I (A -> B -> Prop) R x) (@I (A -> B) y x)). Qed.
Lemma lem6996377 {A B : Type'} (R : type1413 A B) (y : A -> B) (x : A) : (term404 A B R y x) = (term406 A B R y x).
Proof. exact (TRANS (@lem6996372 A B R y x) (@lem6996376 A B R y x)). Qed.
Lemma lem6996378 {A B : Type'} (R : type1413 A B) (y : A -> B) (x : A) : (term403 A B R y x) = (term406 A B R y x).
Proof. exact (TRANS (@lem6996366 A B R y x) (@lem6996377 A B R y x)). Qed.
Lemma lem6996379 {B : Type'} : (@IN B) = (@IN B).
Proof. exact (eq_refl (@IN B)). Qed.
Lemma lem6996384 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996385 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6996384 A B f x). Qed.
Lemma lem6996387 {A B : Type'} (y : A -> B) (x : A) : (y x) = (@I (A -> B) y x).
Proof. exact (@lem6996385 A B y x). Qed.
Lemma lem6996388 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem6996389 {A B : Type'} (y : A -> B) (x : A) : (term407 A B y x) = (term408 A B y x).
Proof. exact (MK_COMB (@lem6996379 B) (@lem6996387 A B y x)). Qed.
Lemma lem6996390 {A B : Type'} (y : A -> B) (x : A) (t : B -> Prop) : (term409 A B y x t) = (term410 A B y x t).
Proof. exact (MK_COMB (@lem6996389 A B y x) (@lem6996388 B t)). Qed.
Lemma lem6996392 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996393 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem6996392 B (type686 B) f x). Qed.
Lemma lem6996394 {A B : Type'} (y : A -> B) (x : A) : (term408 A B y x) = (term411 A B y x).
Proof. exact (@lem6996393 B (@IN B) (@I (A -> B) y x)). Qed.
Lemma lem6996395 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem6996396 {A B : Type'} (y : A -> B) (x : A) (t : B -> Prop) : (term410 A B y x t) = (term412 A B y x t).
Proof. exact (MK_COMB (@lem6996394 A B y x) (@lem6996395 B t)). Qed.
Lemma lem6996398 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996399 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem6996398 (B -> Prop) Prop f x). Qed.
Lemma lem6996400 {A B : Type'} (y : A -> B) (x : A) (t : B -> Prop) : (term412 A B y x t) = (term413 A B y x t).
Proof. exact (@lem6996399 B (term411 A B y x) t). Qed.
Lemma lem6996401 {A B : Type'} (y : A -> B) (x : A) (t : B -> Prop) : (term410 A B y x t) = (term413 A B y x t).
Proof. exact (TRANS (@lem6996396 A B y x t) (@lem6996400 A B y x t)). Qed.
Lemma lem6996402 {A B : Type'} (y : A -> B) (x : A) (t : B -> Prop) : (term409 A B y x t) = (term413 A B y x t).
Proof. exact (TRANS (@lem6996390 A B y x t) (@lem6996401 A B y x t)). Qed.
Lemma lem6996403 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6996404 {A B : Type'} (y : A -> B) (x : A) (t : B -> Prop) : (term414 A B y x t) = (term415 A B y x t).
Proof. exact (MK_COMB (@lem6996403) (@lem6996402 A B y x t)). Qed.
Lemma lem6996405 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term416 A B t R y x) = (term417 A B t R y x).
Proof. exact (MK_COMB (@lem6996404 A B y x t) (@lem6996378 A B R y x)). Qed.
Lemma lem6996406 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6996407 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term418 A B t R y x) = (term419 A B t R y x).
Proof. exact (MK_COMB (@lem6996406) (@lem6996405 A B t R y x)). Qed.
Lemma lem6996408 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term420 A B y t R x) = (term421 A B y t R x).
Proof. exact (MK_COMB (@lem6996407 A B t R y x) (@lem6996354 A B t R x)). Qed.
Lemma lem6996409 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6996416 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996417 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6996416 A (type686 A) f x). Qed.
Lemma lem6996418 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem6996417 A (@IN A) x). Qed.
Lemma lem6996419 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6996420 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem6996418 A x) (@lem6996419 A s)). Qed.
Lemma lem6996422 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6996423 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6996422 (A -> Prop) Prop f x). Qed.
Lemma lem6996424 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term381 A x s).
Proof. exact (@lem6996423 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem6996426 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term381 A x s).
Proof. exact (TRANS (@lem6996420 A x s) (@lem6996424 A x s)). Qed.
Lemma lem6996427 {A : Type'} (x : A) (s : A -> Prop) : (term329 A x s) = (term382 A x s).
Proof. exact (MK_COMB (@lem6996409) (@lem6996426 A x s)). Qed.
Lemma lem6996428 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6996429 {A : Type'} (x : A) (s : A -> Prop) : (term286 A x s) = (term383 A x s).
Proof. exact (MK_COMB (@lem6996428) (@lem6996427 A x s)). Qed.
Lemma lem6996430 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term357 A B s y t R x) = (term422 A B s y t R x).
Proof. exact (MK_COMB (@lem6996429 A x s) (@lem6996408 A B y t R x)). Qed.
Lemma lem6996431 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term359 A B s y t R) = (term423 A B s y t R).
Proof. exact (fun_ext (fun x : A => @lem6996430 A B s y t R x)). Qed.
Lemma lem6996432 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6996433 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term361 A B s y t R) = (term424 A B s y t R).
Proof. exact (MK_COMB (@lem6996432 A) (@lem6996431 A B s y t R)). Qed.
Lemma lem6996434 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term424 A B s y t R.
Proof. exact (EQ_MP (@lem6996433 A B s y t R) (@lem6996039 A B s y t R h1)). Qed.
Lemma lem6996436 {A : Type'} (P : A -> Prop) (Q : Prop) : (term242 A P Q) = (term241 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem6996437 {B : Type'} (P : B -> Prop) (Q : Prop) : (term242 B P Q) = (term241 B P Q).
Proof. exact (@lem6996436 B P Q). Qed.
Lemma lem6996438 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term425 A B _93258 t R x) = (term426 A B _93258 t R x).
Proof. exact (@lem6996437 B (term385 A B t R x) (term377 A B _93258 t R x)). Qed.
Lemma lem6996439 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term427 A B t R x x') = (term384 A B t R x x').
Proof. exact (eq_refl (term427 A B t R x x')). Qed.
Lemma lem6996440 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term428 A B t R x) = (term385 A B t R x).
Proof. exact (fun_ext (fun x' : B => @lem6996439 A B t R x x')). Qed.
Lemma lem6996441 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6996442 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term429 A B t R x) = (term386 A B t R x).
Proof. exact (MK_COMB (@lem6996441 B) (@lem6996440 A B t R x)). Qed.
Lemma lem6996443 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6996444 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term430 A B t R x) = (term387 A B t R x).
Proof. exact (MK_COMB (@lem6996443) (@lem6996442 A B t R x)). Qed.
Lemma lem6996445 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term377 A B _93258 t R x) = (term377 A B _93258 t R x).
Proof. exact (eq_refl (term377 A B _93258 t R x)). Qed.
Lemma lem6996446 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term425 A B _93258 t R x) = (term388 A B _93258 t R x).
Proof. exact (MK_COMB (@lem6996444 A B t R x) (@lem6996445 A B _93258 t R x)). Qed.
Lemma lem6996447 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6996448 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term431 A B _93258 t R x) = (term432 A B _93258 t R x).
Proof. exact (MK_COMB (@lem6996447) (@lem6996446 A B _93258 t R x)). Qed.
Lemma lem6996449 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term427 A B t R x x') = (term384 A B t R x x').
Proof. exact (eq_refl (term427 A B t R x x')). Qed.
Lemma lem6996450 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6996451 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term433 A B t R x x') = (term396 A B t R x x').
Proof. exact (MK_COMB (@lem6996450) (@lem6996449 A B t R x x')). Qed.
Lemma lem6996452 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term377 A B _93258 t R x) = (term377 A B _93258 t R x).
Proof. exact (eq_refl (term377 A B _93258 t R x)). Qed.
Lemma lem6996453 {A B : Type'} (x : B) (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term434 A B x _93258 t R x') = (term435 A B x _93258 t R x').
Proof. exact (MK_COMB (@lem6996451 A B t R x' x) (@lem6996452 A B _93258 t R x')). Qed.
Lemma lem6996454 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term436 A B _93258 t R x) = (term437 A B _93258 t R x).
Proof. exact (fun_ext (fun x' : B => @lem6996453 A B x' _93258 t R x)). Qed.
Lemma lem6996455 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6996456 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term426 A B _93258 t R x) = (term438 A B _93258 t R x).
Proof. exact (MK_COMB (@lem6996455 B) (@lem6996454 A B _93258 t R x)). Qed.
Lemma lem6996457 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : ((term425 A B _93258 t R x) = (term426 A B _93258 t R x)) = ((term388 A B _93258 t R x) = (term438 A B _93258 t R x)).
Proof. exact (MK_COMB (@lem6996448 A B _93258 t R x) (@lem6996456 A B _93258 t R x)). Qed.
Lemma lem6996458 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term388 A B _93258 t R x) = (term438 A B _93258 t R x).
Proof. exact (EQ_MP (@lem6996457 A B _93258 t R x) (@lem6996438 A B _93258 t R x)). Qed.
Lemma lem6996459 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term389 A B _93258 t R) = (term439 A B _93258 t R).
Proof. exact (fun_ext (fun x : A => @lem6996458 A B _93258 t R x)). Qed.
Lemma lem6996460 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6996461 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term390 A B _93258 t R) = (term440 A B _93258 t R).
Proof. exact (MK_COMB (@lem6996460 A) (@lem6996459 A B _93258 t R)). Qed.
Lemma lem6996462 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) : (term391 A B _93258 t) = (term441 A B _93258 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem6996461 A B _93258 t R)). Qed.
Lemma lem6996463 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem6996464 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) : (term392 A B _93258 t) = (term442 A B _93258 t).
Proof. exact (MK_COMB (@lem6996463 A B) (@lem6996462 A B _93258 t)). Qed.
Lemma lem6996465 {A B : Type'} (_93258 : type830 A B) : (term393 A B _93258) = (term443 A B _93258).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6996464 A B _93258 t)). Qed.
Lemma lem6996466 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6996467 {A B : Type'} (_93258 : type830 A B) : (term394 A B _93258) = (term444 A B _93258).
Proof. exact (MK_COMB (@lem6996466 B) (@lem6996465 A B _93258)). Qed.
Lemma lem6996490 {A B : Type'} (x : B) (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term435 A B x _93258 t R x') = (term445 A B x _93258 t R x').
Proof. exact (@lem19490 (term375 A B _93258 R x' t) (term384 A B t R x' x) (term370 A B _93258 t R x')). Qed.
Lemma lem6996491 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term437 A B _93258 t R x) = (term446 A B _93258 t R x).
Proof. exact (fun_ext (fun x' : B => @lem6996490 A B x' _93258 t R x)). Qed.
Lemma lem6996492 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6996493 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term438 A B _93258 t R x) = (term447 A B _93258 t R x).
Proof. exact (MK_COMB (@lem6996492 B) (@lem6996491 A B _93258 t R x)). Qed.
Lemma lem6996494 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term439 A B _93258 t R) = (term448 A B _93258 t R).
Proof. exact (fun_ext (fun x : A => @lem6996493 A B _93258 t R x)). Qed.
Lemma lem6996495 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6996496 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term440 A B _93258 t R) = (term449 A B _93258 t R).
Proof. exact (MK_COMB (@lem6996495 A) (@lem6996494 A B _93258 t R)). Qed.
Lemma lem6996497 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) : (term441 A B _93258 t) = (term450 A B _93258 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem6996496 A B _93258 t R)). Qed.
Lemma lem6996498 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem6996499 {A B : Type'} (_93258 : type830 A B) (t : B -> Prop) : (term442 A B _93258 t) = (term451 A B _93258 t).
Proof. exact (MK_COMB (@lem6996498 A B) (@lem6996497 A B _93258 t)). Qed.
Lemma lem6996500 {A B : Type'} (_93258 : type830 A B) : (term443 A B _93258) = (term452 A B _93258).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6996499 A B _93258 t)). Qed.
Lemma lem6996501 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6996502 {A B : Type'} (_93258 : type830 A B) : (term444 A B _93258) = (term453 A B _93258).
Proof. exact (MK_COMB (@lem6996501 B) (@lem6996500 A B _93258)). Qed.
Lemma lem6996503 {A B : Type'} (_93258 : type830 A B) : (term394 A B _93258) = (term453 A B _93258).
Proof. exact (TRANS (@lem6996467 A B _93258) (@lem6996502 A B _93258)). Qed.
Lemma lem6996504 {A B : Type'} (_93258 : type830 A B) (h1 : term174 A B _93258) : term453 A B _93258.
Proof. exact (EQ_MP (@lem6996503 A B _93258) (@lem6996183 A B _93258 h1)). Qed.
Lemma lem6996518 {A : Type'} (P : Prop) (Q : A -> Prop) : (term292 A P Q) = (term291 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem6996519 {B : Type'} (P : Prop) (Q : B -> Prop) : (term292 B P Q) = (term291 B P Q).
Proof. exact (@lem6996518 B P Q). Qed.
Lemma lem6996520 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term454 A B t R x y) = (term455 A B t R x y).
Proof. exact (@lem6996519 B (term384 A B t R x y) (term398 A B t R x y)). Qed.
Lemma lem6996521 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term456 A B t R x y y') = (term397 A B t R x y' y).
Proof. exact (eq_refl (term456 A B t R x y y')). Qed.
Lemma lem6996522 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term457 A B t R x y) = (term398 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem6996521 A B t R x y' y)). Qed.
Lemma lem6996523 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6996524 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term458 A B t R x y) = (term399 A B t R x y).
Proof. exact (MK_COMB (@lem6996523 B) (@lem6996522 A B t R x y)). Qed.
Lemma lem6996525 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term396 A B t R x y) = (term396 A B t R x y).
Proof. exact (eq_refl (term396 A B t R x y)). Qed.
Lemma lem6996526 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term454 A B t R x y) = (term400 A B t R x y).
Proof. exact (MK_COMB (@lem6996525 A B t R x y) (@lem6996524 A B t R x y)). Qed.
Lemma lem6996527 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6996528 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term459 A B t R x y) = (term460 A B t R x y).
Proof. exact (MK_COMB (@lem6996527) (@lem6996526 A B t R x y)). Qed.
Lemma lem6996529 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term456 A B t R x y y') = (term397 A B t R x y' y).
Proof. exact (eq_refl (term456 A B t R x y y')). Qed.
Lemma lem6996530 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term396 A B t R x y) = (term396 A B t R x y).
Proof. exact (eq_refl (term396 A B t R x y)). Qed.
Lemma lem6996531 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term461 A B t R x y y') = (term462 A B t R x y' y).
Proof. exact (MK_COMB (@lem6996530 A B t R x y) (@lem6996529 A B t R x y' y)). Qed.
Lemma lem6996532 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term463 A B t R x y) = (term464 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem6996531 A B t R x y' y)). Qed.
Lemma lem6996533 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6996534 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term455 A B t R x y) = (term465 A B t R x y).
Proof. exact (MK_COMB (@lem6996533 B) (@lem6996532 A B t R x y)). Qed.
Lemma lem6996535 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : ((term454 A B t R x y) = (term455 A B t R x y)) = ((term400 A B t R x y) = (term465 A B t R x y)).
Proof. exact (MK_COMB (@lem6996528 A B t R x y) (@lem6996534 A B t R x y)). Qed.
Lemma lem6996536 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term400 A B t R x y) = (term465 A B t R x y).
Proof. exact (EQ_MP (@lem6996535 A B t R x y) (@lem6996520 A B t R x y)). Qed.
Lemma lem6996537 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term401 A B t R x) = (term466 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem6996536 A B t R x y)). Qed.
Lemma lem6996538 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6996539 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term402 A B t R x) = (term467 A B t R x).
Proof. exact (MK_COMB (@lem6996538 B) (@lem6996537 A B t R x)). Qed.
Lemma lem6996540 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term419 A B t R y x) = (term419 A B t R y x).
Proof. exact (eq_refl (term419 A B t R y x)). Qed.
Lemma lem6996541 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term421 A B y t R x) = (term468 A B y t R x).
Proof. exact (MK_COMB (@lem6996540 A B t R y x) (@lem6996539 A B t R x)). Qed.
Lemma lem6996543 {A : Type'} (P : Prop) (Q : A -> Prop) : (term469 A P Q) = (term470 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem6996544 {B : Type'} (P : Prop) (Q : B -> Prop) : (term469 B P Q) = (term470 B P Q).
Proof. exact (@lem6996543 B P Q). Qed.
Lemma lem6996545 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term471 A B y t R x) = (term472 A B y t R x).
Proof. exact (@lem6996544 B (term417 A B t R y x) (term466 A B t R x)). Qed.
Lemma lem6996546 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term473 A B t R x y) = (term465 A B t R x y).
Proof. exact (eq_refl (term473 A B t R x y)). Qed.
Lemma lem6996547 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term474 A B t R x) = (term466 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem6996546 A B t R x y)). Qed.
Lemma lem6996548 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6996549 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term475 A B t R x) = (term467 A B t R x).
Proof. exact (MK_COMB (@lem6996548 B) (@lem6996547 A B t R x)). Qed.
Lemma lem6996550 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term419 A B t R y x) = (term419 A B t R y x).
Proof. exact (eq_refl (term419 A B t R y x)). Qed.
Lemma lem6996551 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term471 A B y t R x) = (term468 A B y t R x).
Proof. exact (MK_COMB (@lem6996550 A B t R y x) (@lem6996549 A B t R x)). Qed.
Lemma lem6996552 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6996553 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term476 A B y t R x) = (term477 A B y t R x).
Proof. exact (MK_COMB (@lem6996552) (@lem6996551 A B y t R x)). Qed.
Lemma lem6996554 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term473 A B t R x y) = (term465 A B t R x y).
Proof. exact (eq_refl (term473 A B t R x y)). Qed.
Lemma lem6996555 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term419 A B t R y x) = (term419 A B t R y x).
Proof. exact (eq_refl (term419 A B t R y x)). Qed.
Lemma lem6996556 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term478 A B y t R x y') = (term479 A B y t R x y').
Proof. exact (MK_COMB (@lem6996555 A B t R y x) (@lem6996554 A B t R x y')). Qed.
Lemma lem6996557 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term480 A B y t R x) = (term481 A B y t R x).
Proof. exact (fun_ext (fun y' : B => @lem6996556 A B y t R x y')). Qed.
Lemma lem6996558 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6996559 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term472 A B y t R x) = (term482 A B y t R x).
Proof. exact (MK_COMB (@lem6996558 B) (@lem6996557 A B y t R x)). Qed.
Lemma lem6996560 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : ((term471 A B y t R x) = (term472 A B y t R x)) = ((term468 A B y t R x) = (term482 A B y t R x)).
Proof. exact (MK_COMB (@lem6996553 A B y t R x) (@lem6996559 A B y t R x)). Qed.
Lemma lem6996561 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term468 A B y t R x) = (term482 A B y t R x).
Proof. exact (EQ_MP (@lem6996560 A B y t R x) (@lem6996545 A B y t R x)). Qed.
Lemma lem6996563 {A : Type'} (P : Prop) (Q : A -> Prop) : (term469 A P Q) = (term470 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem6996564 {B : Type'} (P : Prop) (Q : B -> Prop) : (term469 B P Q) = (term470 B P Q).
Proof. exact (@lem6996563 B P Q). Qed.
Lemma lem6996565 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term483 A B y t R x y') = (term484 A B y t R x y').
Proof. exact (@lem6996564 B (term417 A B t R y x) (term464 A B t R x y')). Qed.
Lemma lem6996566 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term485 A B t R x y y') = (term462 A B t R x y' y).
Proof. exact (eq_refl (term485 A B t R x y y')). Qed.
Lemma lem6996567 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term486 A B t R x y) = (term464 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem6996566 A B t R x y' y)). Qed.
Lemma lem6996568 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6996569 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term487 A B t R x y) = (term465 A B t R x y).
Proof. exact (MK_COMB (@lem6996568 B) (@lem6996567 A B t R x y)). Qed.
Lemma lem6996570 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term419 A B t R y x) = (term419 A B t R y x).
Proof. exact (eq_refl (term419 A B t R y x)). Qed.
Lemma lem6996571 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term483 A B y t R x y') = (term479 A B y t R x y').
Proof. exact (MK_COMB (@lem6996570 A B t R y x) (@lem6996569 A B t R x y')). Qed.
Lemma lem6996572 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6996573 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term488 A B y t R x y') = (term489 A B y t R x y').
Proof. exact (MK_COMB (@lem6996572) (@lem6996571 A B y t R x y')). Qed.
Lemma lem6996574 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term485 A B t R x y y') = (term462 A B t R x y' y).
Proof. exact (eq_refl (term485 A B t R x y y')). Qed.
Lemma lem6996575 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term419 A B t R y x) = (term419 A B t R y x).
Proof. exact (eq_refl (term419 A B t R y x)). Qed.
Lemma lem6996576 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term490 A B y t R x y'' y') = (term491 A B y t R x y' y'').
Proof. exact (MK_COMB (@lem6996575 A B t R y x) (@lem6996574 A B t R x y' y'')). Qed.
Lemma lem6996577 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term492 A B y t R x y') = (term493 A B y t R x y').
Proof. exact (fun_ext (fun y'' : B => @lem6996576 A B y t R x y'' y')). Qed.
Lemma lem6996578 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6996579 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term484 A B y t R x y') = (term494 A B y t R x y').
Proof. exact (MK_COMB (@lem6996578 B) (@lem6996577 A B y t R x y')). Qed.
Lemma lem6996580 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : ((term483 A B y t R x y') = (term484 A B y t R x y')) = ((term479 A B y t R x y') = (term494 A B y t R x y')).
Proof. exact (MK_COMB (@lem6996573 A B y t R x y') (@lem6996579 A B y t R x y')). Qed.
Lemma lem6996581 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term479 A B y t R x y') = (term494 A B y t R x y').
Proof. exact (EQ_MP (@lem6996580 A B y t R x y') (@lem6996565 A B y t R x y')). Qed.
Lemma lem6996582 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term481 A B y t R x) = (term495 A B y t R x).
Proof. exact (fun_ext (fun y' : B => @lem6996581 A B y t R x y')). Qed.
Lemma lem6996583 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6996584 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term482 A B y t R x) = (term496 A B y t R x).
Proof. exact (MK_COMB (@lem6996583 B) (@lem6996582 A B y t R x)). Qed.
Lemma lem6996585 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term468 A B y t R x) = (term496 A B y t R x).
Proof. exact (TRANS (@lem6996561 A B y t R x) (@lem6996584 A B y t R x)). Qed.
Lemma lem6996586 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term421 A B y t R x) = (term496 A B y t R x).
Proof. exact (TRANS (@lem6996541 A B y t R x) (@lem6996585 A B y t R x)). Qed.
Lemma lem6996587 {A : Type'} (x : A) (s : A -> Prop) : (term383 A x s) = (term383 A x s).
Proof. exact (eq_refl (term383 A x s)). Qed.
Lemma lem6996588 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term422 A B s y t R x) = (term497 A B s y t R x).
Proof. exact (MK_COMB (@lem6996587 A x s) (@lem6996586 A B y t R x)). Qed.
Lemma lem6996590 {A : Type'} (P : Prop) (Q : A -> Prop) : (term292 A P Q) = (term291 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem6996591 {B : Type'} (P : Prop) (Q : B -> Prop) : (term292 B P Q) = (term291 B P Q).
Proof. exact (@lem6996590 B P Q). Qed.
Lemma lem6996592 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term498 A B s y t R x) = (term499 A B s y t R x).
Proof. exact (@lem6996591 B (term382 A x s) (term495 A B y t R x)). Qed.
Lemma lem6996593 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term500 A B y t R x y') = (term494 A B y t R x y').
Proof. exact (eq_refl (term500 A B y t R x y')). Qed.
Lemma lem6996594 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term501 A B y t R x) = (term495 A B y t R x).
Proof. exact (fun_ext (fun y' : B => @lem6996593 A B y t R x y')). Qed.
Lemma lem6996595 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6996596 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term502 A B y t R x) = (term496 A B y t R x).
Proof. exact (MK_COMB (@lem6996595 B) (@lem6996594 A B y t R x)). Qed.
Lemma lem6996597 {A : Type'} (x : A) (s : A -> Prop) : (term383 A x s) = (term383 A x s).
Proof. exact (eq_refl (term383 A x s)). Qed.
Lemma lem6996598 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term498 A B s y t R x) = (term497 A B s y t R x).
Proof. exact (MK_COMB (@lem6996597 A x s) (@lem6996596 A B y t R x)). Qed.
Lemma lem6996599 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6996600 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term503 A B s y t R x) = (term504 A B s y t R x).
Proof. exact (MK_COMB (@lem6996599) (@lem6996598 A B s y t R x)). Qed.
Lemma lem6996601 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term500 A B y t R x y') = (term494 A B y t R x y').
Proof. exact (eq_refl (term500 A B y t R x y')). Qed.
Lemma lem6996602 {A : Type'} (x : A) (s : A -> Prop) : (term383 A x s) = (term383 A x s).
Proof. exact (eq_refl (term383 A x s)). Qed.
Lemma lem6996603 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term505 A B s y t R x y') = (term506 A B s y t R x y').
Proof. exact (MK_COMB (@lem6996602 A x s) (@lem6996601 A B y t R x y')). Qed.
Lemma lem6996604 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term507 A B s y t R x) = (term508 A B s y t R x).
Proof. exact (fun_ext (fun y' : B => @lem6996603 A B s y t R x y')). Qed.
Lemma lem6996605 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6996606 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term499 A B s y t R x) = (term509 A B s y t R x).
Proof. exact (MK_COMB (@lem6996605 B) (@lem6996604 A B s y t R x)). Qed.
Lemma lem6996607 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : ((term498 A B s y t R x) = (term499 A B s y t R x)) = ((term497 A B s y t R x) = (term509 A B s y t R x)).
Proof. exact (MK_COMB (@lem6996600 A B s y t R x) (@lem6996606 A B s y t R x)). Qed.
Lemma lem6996608 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term497 A B s y t R x) = (term509 A B s y t R x).
Proof. exact (EQ_MP (@lem6996607 A B s y t R x) (@lem6996592 A B s y t R x)). Qed.
Lemma lem6996610 {A : Type'} (P : Prop) (Q : A -> Prop) : (term292 A P Q) = (term291 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem6996611 {B : Type'} (P : Prop) (Q : B -> Prop) : (term292 B P Q) = (term291 B P Q).
Proof. exact (@lem6996610 B P Q). Qed.
Lemma lem6996612 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term510 A B s y t R x y') = (term511 A B s y t R x y').
Proof. exact (@lem6996611 B (term382 A x s) (term493 A B y t R x y')). Qed.
Lemma lem6996613 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term512 A B y t R x y'' y') = (term491 A B y t R x y' y'').
Proof. exact (eq_refl (term512 A B y t R x y'' y')). Qed.
Lemma lem6996614 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term513 A B y t R x y') = (term493 A B y t R x y').
Proof. exact (fun_ext (fun y'' : B => @lem6996613 A B y t R x y'' y')). Qed.
Lemma lem6996615 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6996616 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term514 A B y t R x y') = (term494 A B y t R x y').
Proof. exact (MK_COMB (@lem6996615 B) (@lem6996614 A B y t R x y')). Qed.
Lemma lem6996617 {A : Type'} (x : A) (s : A -> Prop) : (term383 A x s) = (term383 A x s).
Proof. exact (eq_refl (term383 A x s)). Qed.
Lemma lem6996618 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term510 A B s y t R x y') = (term506 A B s y t R x y').
Proof. exact (MK_COMB (@lem6996617 A x s) (@lem6996616 A B y t R x y')). Qed.
Lemma lem6996619 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6996620 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term515 A B s y t R x y') = (term516 A B s y t R x y').
Proof. exact (MK_COMB (@lem6996619) (@lem6996618 A B s y t R x y')). Qed.
Lemma lem6996621 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term512 A B y t R x y'' y') = (term491 A B y t R x y' y'').
Proof. exact (eq_refl (term512 A B y t R x y'' y')). Qed.
Lemma lem6996622 {A : Type'} (x : A) (s : A -> Prop) : (term383 A x s) = (term383 A x s).
Proof. exact (eq_refl (term383 A x s)). Qed.
Lemma lem6996623 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term517 A B s y t R x y'' y') = (term518 A B s y t R x y' y'').
Proof. exact (MK_COMB (@lem6996622 A x s) (@lem6996621 A B y t R x y' y'')). Qed.
Lemma lem6996624 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term519 A B s y t R x y') = (term520 A B s y t R x y').
Proof. exact (fun_ext (fun y'' : B => @lem6996623 A B s y t R x y'' y')). Qed.
Lemma lem6996625 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6996626 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term511 A B s y t R x y') = (term521 A B s y t R x y').
Proof. exact (MK_COMB (@lem6996625 B) (@lem6996624 A B s y t R x y')). Qed.
Lemma lem6996627 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : ((term510 A B s y t R x y') = (term511 A B s y t R x y')) = ((term506 A B s y t R x y') = (term521 A B s y t R x y')).
Proof. exact (MK_COMB (@lem6996620 A B s y t R x y') (@lem6996626 A B s y t R x y')). Qed.
Lemma lem6996628 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term506 A B s y t R x y') = (term521 A B s y t R x y').
Proof. exact (EQ_MP (@lem6996627 A B s y t R x y') (@lem6996612 A B s y t R x y')). Qed.
Lemma lem6996629 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term508 A B s y t R x) = (term522 A B s y t R x).
Proof. exact (fun_ext (fun y' : B => @lem6996628 A B s y t R x y')). Qed.
Lemma lem6996630 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6996631 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term509 A B s y t R x) = (term523 A B s y t R x).
Proof. exact (MK_COMB (@lem6996630 B) (@lem6996629 A B s y t R x)). Qed.
Lemma lem6996632 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term497 A B s y t R x) = (term523 A B s y t R x).
Proof. exact (TRANS (@lem6996608 A B s y t R x) (@lem6996631 A B s y t R x)). Qed.
Lemma lem6996633 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term422 A B s y t R x) = (term523 A B s y t R x).
Proof. exact (TRANS (@lem6996588 A B s y t R x) (@lem6996632 A B s y t R x)). Qed.
Lemma lem6996634 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term423 A B s y t R) = (term524 A B s y t R).
Proof. exact (fun_ext (fun x : A => @lem6996633 A B s y t R x)). Qed.
Lemma lem6996635 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6996636 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term424 A B s y t R) = (term525 A B s y t R).
Proof. exact (MK_COMB (@lem6996635 A) (@lem6996634 A B s y t R)). Qed.
Lemma lem6996674 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term518 A B s y t R x y' y'') = (term526 A B y s t R x y' y'').
Proof. exact (@lem19490 (term417 A B t R y x) (term382 A x s) (term462 A B t R x y' y'')). Qed.
Lemma lem6996675 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term527 A B s t R x y' y) = (term527 A B s t R x y' y).
Proof. exact (eq_refl (term527 A B s t R x y' y)). Qed.
Lemma lem6996682 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term528 A B s t R y x) = (term529 A B t s R y x).
Proof. exact (@lem19490 (term413 A B y x t) (term382 A x s) (term406 A B R y x)). Qed.
Lemma lem6996683 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6996684 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term530 A B s t R y x) = (term531 A B t s R y x).
Proof. exact (MK_COMB (@lem6996683) (@lem6996682 A B t s R y x)). Qed.
Lemma lem6996685 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term526 A B y s t R x y' y'') = (term532 A B y s t R x y' y'').
Proof. exact (MK_COMB (@lem6996684 A B t s R y x) (@lem6996675 A B s t R x y' y'')). Qed.
Lemma lem6996687 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term518 A B s y t R x y' y'') = (term532 A B y s t R x y' y'').
Proof. exact (TRANS (@lem6996674 A B y s t R x y' y'') (@lem6996685 A B y s t R x y' y'')). Qed.
Lemma lem6996688 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term520 A B s y t R x y') = (term533 A B y s t R x y').
Proof. exact (fun_ext (fun y'' : B => @lem6996687 A B y s t R x y'' y')). Qed.
Lemma lem6996689 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6996690 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term521 A B s y t R x y') = (term534 A B y s t R x y').
Proof. exact (MK_COMB (@lem6996689 B) (@lem6996688 A B y s t R x y')). Qed.
Lemma lem6996691 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term522 A B s y t R x) = (term535 A B y s t R x).
Proof. exact (fun_ext (fun y' : B => @lem6996690 A B y s t R x y')). Qed.
Lemma lem6996692 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6996693 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term523 A B s y t R x) = (term536 A B y s t R x).
Proof. exact (MK_COMB (@lem6996692 B) (@lem6996691 A B y s t R x)). Qed.
Lemma lem6996694 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term524 A B s y t R) = (term537 A B y s t R).
Proof. exact (fun_ext (fun x : A => @lem6996693 A B y s t R x)). Qed.
Lemma lem6996695 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6996696 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term525 A B s y t R) = (term538 A B y s t R).
Proof. exact (MK_COMB (@lem6996695 A) (@lem6996694 A B y s t R)). Qed.
Lemma lem6996697 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term424 A B s y t R) = (term538 A B y s t R).
Proof. exact (TRANS (@lem6996636 A B s y t R) (@lem6996696 A B y s t R)). Qed.
Lemma lem6996698 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term538 A B y s t R.
Proof. exact (EQ_MP (@lem6996697 A B y s t R) (@lem6996434 A B s y t R h1)). Qed.
Lemma lem6996699 {A B : Type'} (_93259 : B -> Prop) (_93258 : type830 A B) (h1 : term174 A B _93258) : term539 A B _93258 _93259.
Proof. exact (@lem6996504 A B _93258 h1 _93259). Qed.
Lemma lem6996700 {A B : Type'} (_93258 : type830 A B) (_93259 : B -> Prop) : (term539 A B _93258 _93259) = (term451 A B _93258 _93259).
Proof. exact (eq_refl (term539 A B _93258 _93259)). Qed.
Lemma lem6996701 {A B : Type'} (_93259 : B -> Prop) (_93258 : type830 A B) (h1 : term174 A B _93258) : term451 A B _93258 _93259.
Proof. exact (EQ_MP (@lem6996700 A B _93258 _93259) (@lem6996699 A B _93259 _93258 h1)). Qed.
Lemma lem6996702 {A B : Type'} (_93259 : B -> Prop) (_93260 : type1413 A B) (_93258 : type830 A B) (h1 : term174 A B _93258) : term540 A B _93258 _93259 _93260.
Proof. exact (@lem6996701 A B _93259 _93258 h1 _93260). Qed.
Lemma lem6996703 {A B : Type'} (_93258 : type830 A B) (_93259 : B -> Prop) (_93260 : type1413 A B) : (term540 A B _93258 _93259 _93260) = (term449 A B _93258 _93259 _93260).
Proof. exact (eq_refl (term540 A B _93258 _93259 _93260)). Qed.
Lemma lem6996704 {A B : Type'} (_93259 : B -> Prop) (_93260 : type1413 A B) (_93258 : type830 A B) (h1 : term174 A B _93258) : term449 A B _93258 _93259 _93260.
Proof. exact (EQ_MP (@lem6996703 A B _93258 _93259 _93260) (@lem6996702 A B _93259 _93260 _93258 h1)). Qed.
Lemma lem6996705 {A B : Type'} (_93259 : B -> Prop) (_93260 : type1413 A B) (_93261 : A) (_93258 : type830 A B) (h1 : term174 A B _93258) : term541 A B _93258 _93259 _93260 _93261.
Proof. exact (@lem6996704 A B _93259 _93260 _93258 h1 _93261). Qed.
Lemma lem6996706 {A B : Type'} (_93258 : type830 A B) (_93259 : B -> Prop) (_93260 : type1413 A B) (_93261 : A) : (term541 A B _93258 _93259 _93260 _93261) = (term447 A B _93258 _93259 _93260 _93261).
Proof. exact (eq_refl (term541 A B _93258 _93259 _93260 _93261)). Qed.
Lemma lem6996707 {A B : Type'} (_93259 : B -> Prop) (_93260 : type1413 A B) (_93261 : A) (_93258 : type830 A B) (h1 : term174 A B _93258) : term447 A B _93258 _93259 _93260 _93261.
Proof. exact (EQ_MP (@lem6996706 A B _93258 _93259 _93260 _93261) (@lem6996705 A B _93259 _93260 _93261 _93258 h1)). Qed.
Lemma lem6996708 {A B : Type'} (_93259 : B -> Prop) (_93260 : type1413 A B) (_93261 : A) (_93262 : B) (_93258 : type830 A B) (h1 : term174 A B _93258) : term542 A B _93258 _93259 _93260 _93261 _93262.
Proof. exact (@lem6996707 A B _93259 _93260 _93261 _93258 h1 _93262). Qed.
Lemma lem6996709 {A B : Type'} (_93262 : B) (_93258 : type830 A B) (_93259 : B -> Prop) (_93260 : type1413 A B) (_93261 : A) : (term542 A B _93258 _93259 _93260 _93261 _93262) = (term445 A B _93262 _93258 _93259 _93260 _93261).
Proof. exact (eq_refl (term542 A B _93258 _93259 _93260 _93261 _93262)). Qed.
Lemma lem6996710 {A B : Type'} (_93262 : B) (_93259 : B -> Prop) (_93260 : type1413 A B) (_93261 : A) (_93258 : type830 A B) (h1 : term174 A B _93258) : term445 A B _93262 _93258 _93259 _93260 _93261.
Proof. exact (EQ_MP (@lem6996709 A B _93262 _93258 _93259 _93260 _93261) (@lem6996708 A B _93259 _93260 _93261 _93262 _93258 h1)). Qed.
Lemma lem6996711 {A B : Type'} (_93263 : A) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term543 A B y s t R _93263.
Proof. exact (@lem6996698 A B s y t R h1 _93263). Qed.
Lemma lem6996712 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_93263 : A) : (term543 A B y s t R _93263) = (term536 A B y s t R _93263).
Proof. exact (eq_refl (term543 A B y s t R _93263)). Qed.
Lemma lem6996713 {A B : Type'} (_93263 : A) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term536 A B y s t R _93263.
Proof. exact (EQ_MP (@lem6996712 A B y s t R _93263) (@lem6996711 A B _93263 s y t R h1)). Qed.
Lemma lem6996714 {A B : Type'} (_93263 : A) (_93264 : B) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term544 A B y s t R _93263 _93264.
Proof. exact (@lem6996713 A B _93263 s y t R h1 _93264). Qed.
Lemma lem6996715 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_93263 : A) (_93264 : B) : (term544 A B y s t R _93263 _93264) = (term534 A B y s t R _93263 _93264).
Proof. exact (eq_refl (term544 A B y s t R _93263 _93264)). Qed.
Lemma lem6996716 {A B : Type'} (_93263 : A) (_93264 : B) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term534 A B y s t R _93263 _93264.
Proof. exact (EQ_MP (@lem6996715 A B y s t R _93263 _93264) (@lem6996714 A B _93263 _93264 s y t R h1)). Qed.
Lemma lem6996717 {A B : Type'} (_93263 : A) (_93264 : B) (_93265 : B) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term545 A B y s t R _93263 _93264 _93265.
Proof. exact (@lem6996716 A B _93263 _93264 s y t R h1 _93265). Qed.
Lemma lem6996718 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_93263 : A) (_93265 : B) (_93264 : B) : (term545 A B y s t R _93263 _93264 _93265) = (term532 A B y s t R _93263 _93265 _93264).
Proof. exact (eq_refl (term545 A B y s t R _93263 _93264 _93265)). Qed.
Lemma lem6996719 {A B : Type'} (_93263 : A) (_93265 : B) (_93264 : B) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term532 A B y s t R _93263 _93265 _93264.
Proof. exact (EQ_MP (@lem6996718 A B y s t R _93263 _93265 _93264) (@lem6996717 A B _93263 _93264 _93265 s y t R h1)). Qed.
Lemma lem6996721 {A B : Type'} (_93263 : A) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term529 A B t s R y _93263.
Proof. exact (proj1 (@lem6996719 A B _93263 (@el B) (@el B) s y t R h1)). Qed.
Lemma lem6996725 {A B : Type'} (_93262 : B) (_93260 : type1413 A B) (_93261 : A) (_93259 : B -> Prop) (_93258 : type830 A B) (h1 : term174 A B _93258) : term546 A B _93262 _93258 _93260 _93261 _93259.
Proof. exact (proj1 (@lem6996710 A B _93262 _93259 _93260 _93261 _93258 h1)). Qed.
Lemma lem6996731 {A B : Type'} (_93258 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) (h1 : term226 A B _93258 R x t) : term395 A B _93258 R x t.
Proof. exact (EQ_MP (@lem6996254 A B _93258 R x t) (@lem6996038 A B _93258 R x t h1)). Qed.
Lemma lem6996763 {A B : Type'} (_93263 : A) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term547 A B s y _93263 t.
Proof. exact (proj1 (@lem6996721 A B _93263 s y t R h1)). Qed.
Lemma lem6996769 {A B : Type'} (_93263 : A) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term548 A B s R y _93263.
Proof. exact (proj2 (@lem6996721 A B _93263 s y t R h1)). Qed.
Lemma lem6996780 {A B : Type'} (_93262 : B) (_93258 : type830 A B) (_93260 : type1413 A B) (_93261 : A) (_93259 : B -> Prop) : (term546 A B _93262 _93258 _93260 _93261 _93259) = (term549 A B _93262 _93258 _93260 _93261 _93259).
Proof. exact (@lem6994782 (term382 B _93262 _93259) (term380 A B _93260 _93261 _93262) (term375 A B _93258 _93260 _93261 _93259)). Qed.
Lemma lem6996781 {A B : Type'} (_93262 : B) (_93260 : type1413 A B) (_93261 : A) (_93259 : B -> Prop) (_93258 : type830 A B) (h1 : term174 A B _93258) : term549 A B _93262 _93258 _93260 _93261 _93259.
Proof. exact (EQ_MP (@lem6996780 A B _93262 _93258 _93260 _93261 _93259) (@lem6996725 A B _93262 _93260 _93261 _93259 _93258 h1)). Qed.
Lemma lem6996966 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : term381 A x s.
Proof. exact (EQ_MP (@lem6996209 A x s) (@lem6996032 A x s h1)). Qed.
Lemma lem6996967 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : term550 A x s.
Proof. exact (fun h0 : term382 A x s => @lem6996966 A x s h1). Qed.
Lemma lem6996969 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6996970 {A : Type'} (x : A) (s : A -> Prop) : (term550 A x s) = (term381 A x s).
Proof. exact (@lem6996969 (term381 A x s)). Qed.
Lemma lem6996971 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : term381 A x s.
Proof. exact (EQ_MP (@lem6996970 A x s) (@lem6996967 A x s h1)). Qed.
Lemma lem6996977 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6996978 {A B : Type'} (y : A -> B) (t : B -> Prop) (_93263 : A) (s : A -> Prop) : (term547 A B s y _93263 t) = (term552 A B y t _93263 s).
Proof. exact (@lem6996977 (term413 A B y _93263 t) (term382 A _93263 s)). Qed.
Lemma lem6996984 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6996985 {A B : Type'} (y : A -> B) (t : B -> Prop) (_93263 : A) (s : A -> Prop) : (term553 A B s y _93263 t) = (term554 A B y t _93263 s).
Proof. exact (MK_COMB (@lem6996984) (@lem6996978 A B y t _93263 s)). Qed.
Lemma lem6996991 {A B : Type'} (y : A -> B) (t : B -> Prop) (_93263 : A) (s : A -> Prop) : (term552 A B y t _93263 s) = (term552 A B y t _93263 s).
Proof. exact (eq_refl (term552 A B y t _93263 s)). Qed.
Lemma lem6996992 {A B : Type'} (y : A -> B) (t : B -> Prop) (_93263 : A) (s : A -> Prop) : ((term547 A B s y _93263 t) = (term552 A B y t _93263 s)) = ((term552 A B y t _93263 s) = (term552 A B y t _93263 s)).
Proof. exact (MK_COMB (@lem6996985 A B y t _93263 s) (@lem6996991 A B y t _93263 s)). Qed.
Lemma lem6996994 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6996995 (x : Prop) : (x = x) = True.
Proof. exact (@lem6996994 Prop x). Qed.
Lemma lem6996996 {A B : Type'} (y : A -> B) (t : B -> Prop) (_93263 : A) (s : A -> Prop) : ((term552 A B y t _93263 s) = (term552 A B y t _93263 s)) = True.
Proof. exact (@lem6996995 (term552 A B y t _93263 s)). Qed.
Lemma lem6996997 {A B : Type'} (y : A -> B) (t : B -> Prop) (_93263 : A) (s : A -> Prop) : ((term547 A B s y _93263 t) = (term552 A B y t _93263 s)) = True.
Proof. exact (TRANS (@lem6996992 A B y t _93263 s) (@lem6996996 A B y t _93263 s)). Qed.
Lemma lem6996998 {A B : Type'} (y : A -> B) (t : B -> Prop) (_93263 : A) (s : A -> Prop) : True = ((term547 A B s y _93263 t) = (term552 A B y t _93263 s)).
Proof. exact (SYM (@lem6996997 A B y t _93263 s)). Qed.
Lemma lem6996999 {A B : Type'} (y : A -> B) (t : B -> Prop) (_93263 : A) (s : A -> Prop) : (term547 A B s y _93263 t) = (term552 A B y t _93263 s).
Proof. exact (EQ_MP (@lem6996998 A B y t _93263 s) (@lem0)). Qed.
Lemma lem6997000 {A B : Type'} (_93263 : A) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term552 A B y t _93263 s.
Proof. exact (EQ_MP (@lem6996999 A B y t _93263 s) (@lem6996763 A B _93263 s y t R h1)). Qed.
Lemma lem6997002 (b : Prop) (a : Prop) : (a \/ b) = (term555 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6997003 {A B : Type'} (s : A -> Prop) (y : A -> B) (_93263 : A) (t : B -> Prop) : (term552 A B y t _93263 s) = (term556 A B s y _93263 t).
Proof. exact (@lem6997002 (term382 A _93263 s) (term413 A B y _93263 t)). Qed.
Lemma lem6997005 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6997006 {A : Type'} (_93263 : A) (s : A -> Prop) : (term557 A _93263 s) = (term381 A _93263 s).
Proof. exact (@lem6997005 (term381 A _93263 s)). Qed.
Lemma lem6997007 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6997008 {A : Type'} (_93263 : A) (s : A -> Prop) : (term558 A _93263 s) = (term559 A _93263 s).
Proof. exact (MK_COMB (@lem6997007) (@lem6997006 A _93263 s)). Qed.
Lemma lem6997009 {A B : Type'} (y : A -> B) (_93263 : A) (t : B -> Prop) : (term413 A B y _93263 t) = (term413 A B y _93263 t).
Proof. exact (eq_refl (term413 A B y _93263 t)). Qed.
Lemma lem6997010 {A B : Type'} (s : A -> Prop) (y : A -> B) (_93263 : A) (t : B -> Prop) : (term556 A B s y _93263 t) = (term560 A B s y _93263 t).
Proof. exact (MK_COMB (@lem6997008 A _93263 s) (@lem6997009 A B y _93263 t)). Qed.
Lemma lem6997011 {A B : Type'} (s : A -> Prop) (y : A -> B) (_93263 : A) (t : B -> Prop) : (term552 A B y t _93263 s) = (term560 A B s y _93263 t).
Proof. exact (TRANS (@lem6997003 A B s y _93263 t) (@lem6997010 A B s y _93263 t)). Qed.
Lemma lem6997014 {A B : Type'} (_93263 : A) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term560 A B s y _93263 t.
Proof. exact (EQ_MP (@lem6997011 A B s y _93263 t) (@lem6997000 A B _93263 s y t R h1)). Qed.
Lemma lem6997015 {A B : Type'} (_93263 : A) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term560 A B s y _93263 t.
Proof. exact (@lem6997014 A B _93263 s y t R h1). Qed.
Lemma lem6997016 {A B : Type'} (x : A) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term560 A B s y x t.
Proof. exact (@lem6997015 A B x s y t R h1). Qed.
Lemma lem6997019 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (s : A -> Prop) (h1 : term361 A B s y t R) (h2 : @IN A x s) : term413 A B y x t.
Proof. exact (@lem6997016 A B x s y t R h1 (@lem6996971 A x s h2)). Qed.
Lemma lem6997020 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (s : A -> Prop) (h1 : term361 A B s y t R) (h2 : @IN A x s) : term561 A B y x t.
Proof. exact (fun h0 : term562 A B y x t => @lem6997019 A B y t R x s h1 h2). Qed.
Lemma lem6997022 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6997023 {A B : Type'} (y : A -> B) (x : A) (t : B -> Prop) : (term561 A B y x t) = (term413 A B y x t).
Proof. exact (@lem6997022 (term413 A B y x t)). Qed.
Lemma lem6997024 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (s : A -> Prop) (h1 : term361 A B s y t R) (h2 : @IN A x s) : term413 A B y x t.
Proof. exact (EQ_MP (@lem6997023 A B y x t) (@lem6997020 A B y t R x s h1 h2)). Qed.
Lemma lem6997026 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : term381 A x s.
Proof. exact (EQ_MP (@lem6996209 A x s) (@lem6996032 A x s h1)). Qed.
Lemma lem6997027 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : term550 A x s.
Proof. exact (fun h0 : term382 A x s => @lem6997026 A x s h1). Qed.
Lemma lem6997029 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6997030 {A : Type'} (x : A) (s : A -> Prop) : (term550 A x s) = (term381 A x s).
Proof. exact (@lem6997029 (term381 A x s)). Qed.
Lemma lem6997031 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : term381 A x s.
Proof. exact (EQ_MP (@lem6997030 A x s) (@lem6997027 A x s h1)). Qed.
Lemma lem6997037 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6997038 {A B : Type'} (R : type1413 A B) (y : A -> B) (_93263 : A) (s : A -> Prop) : (term548 A B s R y _93263) = (term563 A B R y _93263 s).
Proof. exact (@lem6997037 (term406 A B R y _93263) (term382 A _93263 s)). Qed.
Lemma lem6997044 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6997045 {A B : Type'} (R : type1413 A B) (y : A -> B) (_93263 : A) (s : A -> Prop) : (term564 A B s R y _93263) = (term565 A B R y _93263 s).
Proof. exact (MK_COMB (@lem6997044) (@lem6997038 A B R y _93263 s)). Qed.
Lemma lem6997051 {A B : Type'} (R : type1413 A B) (y : A -> B) (_93263 : A) (s : A -> Prop) : (term563 A B R y _93263 s) = (term563 A B R y _93263 s).
Proof. exact (eq_refl (term563 A B R y _93263 s)). Qed.
Lemma lem6997052 {A B : Type'} (R : type1413 A B) (y : A -> B) (_93263 : A) (s : A -> Prop) : ((term548 A B s R y _93263) = (term563 A B R y _93263 s)) = ((term563 A B R y _93263 s) = (term563 A B R y _93263 s)).
Proof. exact (MK_COMB (@lem6997045 A B R y _93263 s) (@lem6997051 A B R y _93263 s)). Qed.
Lemma lem6997054 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6997055 (x : Prop) : (x = x) = True.
Proof. exact (@lem6997054 Prop x). Qed.
Lemma lem6997056 {A B : Type'} (R : type1413 A B) (y : A -> B) (_93263 : A) (s : A -> Prop) : ((term563 A B R y _93263 s) = (term563 A B R y _93263 s)) = True.
Proof. exact (@lem6997055 (term563 A B R y _93263 s)). Qed.
Lemma lem6997057 {A B : Type'} (R : type1413 A B) (y : A -> B) (_93263 : A) (s : A -> Prop) : ((term548 A B s R y _93263) = (term563 A B R y _93263 s)) = True.
Proof. exact (TRANS (@lem6997052 A B R y _93263 s) (@lem6997056 A B R y _93263 s)). Qed.
Lemma lem6997058 {A B : Type'} (R : type1413 A B) (y : A -> B) (_93263 : A) (s : A -> Prop) : True = ((term548 A B s R y _93263) = (term563 A B R y _93263 s)).
Proof. exact (SYM (@lem6997057 A B R y _93263 s)). Qed.
Lemma lem6997059 {A B : Type'} (R : type1413 A B) (y : A -> B) (_93263 : A) (s : A -> Prop) : (term548 A B s R y _93263) = (term563 A B R y _93263 s).
Proof. exact (EQ_MP (@lem6997058 A B R y _93263 s) (@lem0)). Qed.
Lemma lem6997060 {A B : Type'} (_93263 : A) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term563 A B R y _93263 s.
Proof. exact (EQ_MP (@lem6997059 A B R y _93263 s) (@lem6996769 A B _93263 s y t R h1)). Qed.
Lemma lem6997062 (b : Prop) (a : Prop) : (a \/ b) = (term555 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6997063 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (y : A -> B) (_93263 : A) : (term563 A B R y _93263 s) = (term566 A B s R y _93263).
Proof. exact (@lem6997062 (term382 A _93263 s) (term406 A B R y _93263)). Qed.
Lemma lem6997065 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6997066 {A : Type'} (_93263 : A) (s : A -> Prop) : (term557 A _93263 s) = (term381 A _93263 s).
Proof. exact (@lem6997065 (term381 A _93263 s)). Qed.
Lemma lem6997067 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6997068 {A : Type'} (_93263 : A) (s : A -> Prop) : (term558 A _93263 s) = (term559 A _93263 s).
Proof. exact (MK_COMB (@lem6997067) (@lem6997066 A _93263 s)). Qed.
Lemma lem6997069 {A B : Type'} (R : type1413 A B) (y : A -> B) (_93263 : A) : (term406 A B R y _93263) = (term406 A B R y _93263).
Proof. exact (eq_refl (term406 A B R y _93263)). Qed.
Lemma lem6997070 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (y : A -> B) (_93263 : A) : (term566 A B s R y _93263) = (term567 A B s R y _93263).
Proof. exact (MK_COMB (@lem6997068 A _93263 s) (@lem6997069 A B R y _93263)). Qed.
Lemma lem6997071 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (y : A -> B) (_93263 : A) : (term563 A B R y _93263 s) = (term567 A B s R y _93263).
Proof. exact (TRANS (@lem6997063 A B s R y _93263) (@lem6997070 A B s R y _93263)). Qed.
Lemma lem6997074 {A B : Type'} (_93263 : A) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term567 A B s R y _93263.
Proof. exact (EQ_MP (@lem6997071 A B s R y _93263) (@lem6997060 A B _93263 s y t R h1)). Qed.
Lemma lem6997075 {A B : Type'} (_93263 : A) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term567 A B s R y _93263.
Proof. exact (@lem6997074 A B _93263 s y t R h1). Qed.
Lemma lem6997076 {A B : Type'} (x : A) (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (h1 : term361 A B s y t R) : term567 A B s R y x.
Proof. exact (@lem6997075 A B x s y t R h1). Qed.
Lemma lem6997079 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (s : A -> Prop) (h1 : term361 A B s y t R) (h2 : @IN A x s) : term406 A B R y x.
Proof. exact (@lem6997076 A B x s y t R h1 (@lem6997031 A x s h2)). Qed.
Lemma lem6997080 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (s : A -> Prop) (h1 : term361 A B s y t R) (h2 : @IN A x s) : term568 A B R y x.
Proof. exact (fun h0 : term569 A B R y x => @lem6997079 A B y t R x s h1 h2). Qed.
Lemma lem6997082 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6997083 {A B : Type'} (R : type1413 A B) (y : A -> B) (x : A) : (term568 A B R y x) = (term406 A B R y x).
Proof. exact (@lem6997082 (term406 A B R y x)). Qed.
Lemma lem6997084 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (s : A -> Prop) (h1 : term361 A B s y t R) (h2 : @IN A x s) : term406 A B R y x.
Proof. exact (EQ_MP (@lem6997083 A B R y x) (@lem6997080 A B y t R x s h1 h2)). Qed.
Lemma lem6997090 (q : Prop) (p : Prop) (r : Prop) : (term21 p q r) = (term21 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6997091 {A B : Type'} (_93262 : B) (_93258 : type830 A B) (_93260 : type1413 A B) (_93261 : A) (_93259 : B -> Prop) : (term549 A B _93262 _93258 _93260 _93261 _93259) = (term570 A B _93262 _93258 _93260 _93261 _93259).
Proof. exact (@lem6997090 (term380 A B _93260 _93261 _93262) (term382 B _93262 _93259) (term375 A B _93258 _93260 _93261 _93259)). Qed.
Lemma lem6997105 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6997106 {A B : Type'} (_93258 : type830 A B) (_93260 : type1413 A B) (_93261 : A) (_93262 : B) (_93259 : B -> Prop) : (term571 A B _93262 _93258 _93260 _93261 _93259) = (term572 A B _93258 _93260 _93261 _93262 _93259).
Proof. exact (@lem6997105 (term375 A B _93258 _93260 _93261 _93259) (term382 B _93262 _93259)). Qed.
Lemma lem6997112 {A B : Type'} (_93260 : type1413 A B) (_93261 : A) (_93262 : B) : (term573 A B _93260 _93261 _93262) = (term573 A B _93260 _93261 _93262).
Proof. exact (eq_refl (term573 A B _93260 _93261 _93262)). Qed.
Lemma lem6997113 {A B : Type'} (_93258 : type830 A B) (_93260 : type1413 A B) (_93261 : A) (_93262 : B) (_93259 : B -> Prop) : (term570 A B _93262 _93258 _93260 _93261 _93259) = (term574 A B _93258 _93260 _93261 _93262 _93259).
Proof. exact (MK_COMB (@lem6997112 A B _93260 _93261 _93262) (@lem6997106 A B _93258 _93260 _93261 _93262 _93259)). Qed.
Lemma lem6997117 (q : Prop) (p : Prop) (r : Prop) : (term21 p q r) = (term21 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6997118 {A B : Type'} (_93258 : type830 A B) (_93260 : type1413 A B) (_93261 : A) (_93262 : B) (_93259 : B -> Prop) : (term574 A B _93258 _93260 _93261 _93262 _93259) = (term575 A B _93258 _93260 _93261 _93262 _93259).
Proof. exact (@lem6997117 (term375 A B _93258 _93260 _93261 _93259) (term380 A B _93260 _93261 _93262) (term382 B _93262 _93259)). Qed.
Lemma lem6997134 {A B : Type'} (_93258 : type830 A B) (_93260 : type1413 A B) (_93261 : A) (_93262 : B) (_93259 : B -> Prop) : (term570 A B _93262 _93258 _93260 _93261 _93259) = (term575 A B _93258 _93260 _93261 _93262 _93259).
Proof. exact (TRANS (@lem6997113 A B _93258 _93260 _93261 _93262 _93259) (@lem6997118 A B _93258 _93260 _93261 _93262 _93259)). Qed.
Lemma lem6997135 {A B : Type'} (_93258 : type830 A B) (_93260 : type1413 A B) (_93261 : A) (_93262 : B) (_93259 : B -> Prop) : (term549 A B _93262 _93258 _93260 _93261 _93259) = (term575 A B _93258 _93260 _93261 _93262 _93259).
Proof. exact (TRANS (@lem6997091 A B _93262 _93258 _93260 _93261 _93259) (@lem6997134 A B _93258 _93260 _93261 _93262 _93259)). Qed.
Lemma lem6997136 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6997137 {A B : Type'} (_93258 : type830 A B) (_93260 : type1413 A B) (_93261 : A) (_93262 : B) (_93259 : B -> Prop) : (term576 A B _93262 _93258 _93260 _93261 _93259) = (term577 A B _93258 _93260 _93261 _93262 _93259).
Proof. exact (MK_COMB (@lem6997136) (@lem6997135 A B _93258 _93260 _93261 _93262 _93259)). Qed.
Lemma lem6997151 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6997152 {A B : Type'} (_93260 : type1413 A B) (_93261 : A) (_93262 : B) (_93259 : B -> Prop) : (term384 A B _93259 _93260 _93261 _93262) = (term578 A B _93260 _93261 _93262 _93259).
Proof. exact (@lem6997151 (term380 A B _93260 _93261 _93262) (term382 B _93262 _93259)). Qed.
Lemma lem6997158 {A B : Type'} (_93258 : type830 A B) (_93260 : type1413 A B) (_93261 : A) (_93259 : B -> Prop) : (term579 A B _93258 _93260 _93261 _93259) = (term579 A B _93258 _93260 _93261 _93259).
Proof. exact (eq_refl (term579 A B _93258 _93260 _93261 _93259)). Qed.
Lemma lem6997159 {A B : Type'} (_93258 : type830 A B) (_93260 : type1413 A B) (_93261 : A) (_93262 : B) (_93259 : B -> Prop) : (term580 A B _93258 _93259 _93260 _93261 _93262) = (term575 A B _93258 _93260 _93261 _93262 _93259).
Proof. exact (MK_COMB (@lem6997158 A B _93258 _93260 _93261 _93259) (@lem6997152 A B _93260 _93261 _93262 _93259)). Qed.
Lemma lem6997170 {A B : Type'} (_93258 : type830 A B) (_93260 : type1413 A B) (_93261 : A) (_93262 : B) (_93259 : B -> Prop) : ((term549 A B _93262 _93258 _93260 _93261 _93259) = (term580 A B _93258 _93259 _93260 _93261 _93262)) = ((term575 A B _93258 _93260 _93261 _93262 _93259) = (term575 A B _93258 _93260 _93261 _93262 _93259)).
Proof. exact (MK_COMB (@lem6997137 A B _93258 _93260 _93261 _93262 _93259) (@lem6997159 A B _93258 _93260 _93261 _93262 _93259)). Qed.
Lemma lem6997172 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6997173 (x : Prop) : (x = x) = True.
Proof. exact (@lem6997172 Prop x). Qed.
Lemma lem6997174 {A B : Type'} (_93258 : type830 A B) (_93260 : type1413 A B) (_93261 : A) (_93262 : B) (_93259 : B -> Prop) : ((term575 A B _93258 _93260 _93261 _93262 _93259) = (term575 A B _93258 _93260 _93261 _93262 _93259)) = True.
Proof. exact (@lem6997173 (term575 A B _93258 _93260 _93261 _93262 _93259)). Qed.
Lemma lem6997175 {A B : Type'} (_93258 : type830 A B) (_93259 : B -> Prop) (_93260 : type1413 A B) (_93261 : A) (_93262 : B) : ((term549 A B _93262 _93258 _93260 _93261 _93259) = (term580 A B _93258 _93259 _93260 _93261 _93262)) = True.
Proof. exact (TRANS (@lem6997170 A B _93258 _93260 _93261 _93262 _93259) (@lem6997174 A B _93258 _93260 _93261 _93262 _93259)). Qed.
Lemma lem6997176 {A B : Type'} (_93258 : type830 A B) (_93259 : B -> Prop) (_93260 : type1413 A B) (_93261 : A) (_93262 : B) : True = ((term549 A B _93262 _93258 _93260 _93261 _93259) = (term580 A B _93258 _93259 _93260 _93261 _93262)).
Proof. exact (SYM (@lem6997175 A B _93258 _93259 _93260 _93261 _93262)). Qed.
Lemma lem6997177 {A B : Type'} (_93258 : type830 A B) (_93259 : B -> Prop) (_93260 : type1413 A B) (_93261 : A) (_93262 : B) : (term549 A B _93262 _93258 _93260 _93261 _93259) = (term580 A B _93258 _93259 _93260 _93261 _93262).
Proof. exact (EQ_MP (@lem6997176 A B _93258 _93259 _93260 _93261 _93262) (@lem0)). Qed.
Lemma lem6997178 {A B : Type'} (_93259 : B -> Prop) (_93260 : type1413 A B) (_93261 : A) (_93262 : B) (_93258 : type830 A B) (h1 : term174 A B _93258) : term580 A B _93258 _93259 _93260 _93261 _93262.
Proof. exact (EQ_MP (@lem6997177 A B _93258 _93259 _93260 _93261 _93262) (@lem6996781 A B _93262 _93260 _93261 _93259 _93258 h1)). Qed.
Lemma lem6997180 (b : Prop) (a : Prop) : (a \/ b) = (term555 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6997181 {A B : Type'} (_93262 : B) (_93258 : type830 A B) (_93260 : type1413 A B) (_93261 : A) (_93259 : B -> Prop) : (term580 A B _93258 _93259 _93260 _93261 _93262) = (term581 A B _93262 _93258 _93260 _93261 _93259).
Proof. exact (@lem6997180 (term384 A B _93259 _93260 _93261 _93262) (term375 A B _93258 _93260 _93261 _93259)). Qed.
Lemma lem6997183 (a : Prop) (b : Prop) : (term582 a b) = (term583 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6997184 {A B : Type'} (_93259 : B -> Prop) (_93260 : type1413 A B) (_93261 : A) (_93262 : B) : (term584 A B _93259 _93260 _93261 _93262) = (term585 A B _93259 _93260 _93261 _93262).
Proof. exact (@lem6997183 (term382 B _93262 _93259) (term380 A B _93260 _93261 _93262)). Qed.
Lemma lem6997186 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6997187 {B : Type'} (_93262 : B) (_93259 : B -> Prop) : (term557 B _93262 _93259) = (term381 B _93262 _93259).
Proof. exact (@lem6997186 (term381 B _93262 _93259)). Qed.
Lemma lem6997188 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6997189 {B : Type'} (_93262 : B) (_93259 : B -> Prop) : (term586 B _93262 _93259) = (term587 B _93262 _93259).
Proof. exact (MK_COMB (@lem6997188) (@lem6997187 B _93262 _93259)). Qed.
Lemma lem6997191 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6997192 {A B : Type'} (_93260 : type1413 A B) (_93261 : A) (_93262 : B) : (term588 A B _93260 _93261 _93262) = (term378 A B _93260 _93261 _93262).
Proof. exact (@lem6997191 (term378 A B _93260 _93261 _93262)). Qed.
Lemma lem6997193 {A B : Type'} (_93259 : B -> Prop) (_93260 : type1413 A B) (_93261 : A) (_93262 : B) : (term585 A B _93259 _93260 _93261 _93262) = (term589 A B _93259 _93260 _93261 _93262).
Proof. exact (MK_COMB (@lem6997189 B _93262 _93259) (@lem6997192 A B _93260 _93261 _93262)). Qed.
Lemma lem6997194 {A B : Type'} (_93259 : B -> Prop) (_93260 : type1413 A B) (_93261 : A) (_93262 : B) : (term584 A B _93259 _93260 _93261 _93262) = (term589 A B _93259 _93260 _93261 _93262).
Proof. exact (TRANS (@lem6997184 A B _93259 _93260 _93261 _93262) (@lem6997193 A B _93259 _93260 _93261 _93262)). Qed.
Lemma lem6997195 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6997196 {A B : Type'} (_93259 : B -> Prop) (_93260 : type1413 A B) (_93261 : A) (_93262 : B) : (term590 A B _93259 _93260 _93261 _93262) = (term591 A B _93259 _93260 _93261 _93262).
Proof. exact (MK_COMB (@lem6997195) (@lem6997194 A B _93259 _93260 _93261 _93262)). Qed.
Lemma lem6997197 {A B : Type'} (_93258 : type830 A B) (_93260 : type1413 A B) (_93261 : A) (_93259 : B -> Prop) : (term375 A B _93258 _93260 _93261 _93259) = (term375 A B _93258 _93260 _93261 _93259).
Proof. exact (eq_refl (term375 A B _93258 _93260 _93261 _93259)). Qed.
Lemma lem6997198 {A B : Type'} (_93262 : B) (_93258 : type830 A B) (_93260 : type1413 A B) (_93261 : A) (_93259 : B -> Prop) : (term581 A B _93262 _93258 _93260 _93261 _93259) = (term592 A B _93262 _93258 _93260 _93261 _93259).
Proof. exact (MK_COMB (@lem6997196 A B _93259 _93260 _93261 _93262) (@lem6997197 A B _93258 _93260 _93261 _93259)). Qed.
Lemma lem6997199 {A B : Type'} (_93262 : B) (_93258 : type830 A B) (_93260 : type1413 A B) (_93261 : A) (_93259 : B -> Prop) : (term580 A B _93258 _93259 _93260 _93261 _93262) = (term592 A B _93262 _93258 _93260 _93261 _93259).
Proof. exact (TRANS (@lem6997181 A B _93262 _93258 _93260 _93261 _93259) (@lem6997198 A B _93262 _93258 _93260 _93261 _93259)). Qed.
Lemma lem6997201 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (s : A -> Prop) (h1 : term361 A B s y t R) (h2 : @IN A x s) : term417 A B t R y x.
Proof. exact (conj (@lem6997024 A B y t R x s h1 h2) (@lem6997084 A B y t R x s h1 h2)). Qed.
Lemma lem6997203 {A B : Type'} (_93262 : B) (_93260 : type1413 A B) (_93261 : A) (_93259 : B -> Prop) (_93258 : type830 A B) (h1 : term174 A B _93258) : term592 A B _93262 _93258 _93260 _93261 _93259.
Proof. exact (EQ_MP (@lem6997199 A B _93262 _93258 _93260 _93261 _93259) (@lem6997178 A B _93259 _93260 _93261 _93262 _93258 h1)). Qed.
Lemma lem6997204 {A B : Type'} (_93262 : B) (_93260 : type1413 A B) (_93261 : A) (_93259 : B -> Prop) (_93258 : type830 A B) (h1 : term174 A B _93258) : term592 A B _93262 _93258 _93260 _93261 _93259.
Proof. exact (@lem6997203 A B _93262 _93260 _93261 _93259 _93258 h1). Qed.
Lemma lem6997205 {A B : Type'} (y : A -> B) (R : type1413 A B) (x : A) (t : B -> Prop) (_93258 : type830 A B) (h1 : term174 A B _93258) : term593 A B y _93258 R x t.
Proof. exact (@lem6997204 A B (@I (A -> B) y x) R x t _93258 h1). Qed.
Lemma lem6997208 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (_93258 : type830 A B) (x : A) (s : A -> Prop) (h1 : term361 A B s y t R) (h2 : term174 A B _93258) (h3 : @IN A x s) : term375 A B _93258 R x t.
Proof. exact (@lem6997205 A B y R x t _93258 h2 (@lem6997201 A B y t R x s h1 h3)). Qed.
Lemma lem6997209 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (_93258 : type830 A B) (x : A) (s : A -> Prop) (h1 : term361 A B s y t R) (h2 : term174 A B _93258) (h3 : @IN A x s) : term594 A B _93258 R x t.
Proof. exact (fun h0 : term395 A B _93258 R x t => @lem6997208 A B y t R _93258 x s h1 h2 h3). Qed.
Lemma lem6997211 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6997212 {A B : Type'} (_93258 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term594 A B _93258 R x t) = (term375 A B _93258 R x t).
Proof. exact (@lem6997211 (term375 A B _93258 R x t)). Qed.
Lemma lem6997213 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (_93258 : type830 A B) (x : A) (s : A -> Prop) (h1 : term361 A B s y t R) (h2 : term174 A B _93258) (h3 : @IN A x s) : term375 A B _93258 R x t.
Proof. exact (EQ_MP (@lem6997212 A B _93258 R x t) (@lem6997209 A B y t R _93258 x s h1 h2 h3)). Qed.
Lemma lem6997216 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6997218 {A B : Type'} (_93258 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) : (term395 A B _93258 R x t) = (term595 A B _93258 R x t).
Proof. exact (@lem6997216 (term375 A B _93258 R x t)). Qed.
Lemma lem6997221 {A B : Type'} (_93258 : type830 A B) (R : type1413 A B) (x : A) (t : B -> Prop) (h1 : term226 A B _93258 R x t) : term595 A B _93258 R x t.
Proof. exact (EQ_MP (@lem6997218 A B _93258 R x t) (@lem6996731 A B _93258 R x t h1)). Qed.
Lemma lem6997224 {A B : Type'} (y : A -> B) (_93258 : type830 A B) (R : type1413 A B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term361 A B s y t R) (h2 : term174 A B _93258) (h3 : term226 A B _93258 R x t) (h4 : @IN A x s) : False.
Proof. exact (@lem6997221 A B _93258 R x t h3 (@lem6997213 A B y t R _93258 x s h1 h2 h4)). Qed.
Lemma lem6997225 {A B : Type'} (y : A -> B) (_93258 : type830 A B) (R : type1413 A B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term361 A B s y t R) (h2 : term174 A B _93258) (h3 : term226 A B _93258 R x t) (h4 : @IN A x s) : term596.
Proof. exact (fun h0 : ~ False => @lem6997224 A B y _93258 R t x s h1 h2 h3 h4). Qed.
Lemma lem6997227 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6997228 : term596 = False.
Proof. exact (@lem6997227 False). Qed.
Lemma lem6997229 {A B : Type'} (y : A -> B) (_93258 : type830 A B) (R : type1413 A B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term361 A B s y t R) (h2 : term174 A B _93258) (h3 : term226 A B _93258 R x t) (h4 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem6997228) (@lem6997225 A B y _93258 R t x s h1 h2 h3 h4)). Qed.
Lemma lem6997230 {A B : Type'} (_93258 : type830 A B) (R : type1413 A B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : term174 A B _93258) (h3 : term226 A B _93258 R x t) (h4 : @IN A x s) : False.
Proof. exact (ex_elim (@lem6996026 A B s t R h1) (fun y : A -> B => fun h0 : term363 A B s t R y => @lem6997229 A B y _93258 R t x s h0 h2 h3 h4)). Qed.
Lemma lem6997231 {A B : Type'} (_93258 : type830 A B) (R : type1413 A B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : term174 A B _93258) (h3 : term226 A B _93258 R x t) (h4 : @IN A x s) : (term226 A B _93258 R x t) = False.
Proof. exact (prop_ext (fun h5 : term226 A B _93258 R x t => @lem6997230 A B _93258 R t x s h1 h2 h3 h4) (fun h5 : False => @lem6996038 A B _93258 R x t h3)). Qed.
Lemma lem6997232 {A B : Type'} (_93258 : type830 A B) (R : type1413 A B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : term174 A B _93258) (h3 : term226 A B _93258 R x t) (h4 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem6997231 A B _93258 R t x s h1 h2 h3 h4) (@lem6996038 A B _93258 R x t h3)). Qed.
Lemma lem6997233 {A B : Type'} (_93258 : type830 A B) (R : type1413 A B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : term174 A B _93258) (h3 : term226 A B _93258 R x t) (h4 : @IN A x s) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h5 : @IN A x s => @lem6997232 A B _93258 R t x s h1 h2 h3 h4) (fun h5 : False => @lem6996032 A x s h4)). Qed.
Lemma lem6997234 {A B : Type'} (_93258 : type830 A B) (R : type1413 A B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : term174 A B _93258) (h3 : term226 A B _93258 R x t) (h4 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem6997233 A B _93258 R t x s h1 h2 h3 h4) (@lem6996032 A x s h4)). Qed.
Lemma lem6997235 {A B : Type'} (_93258 : type830 A B) (R : type1413 A B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : term174 A B _93258) (h3 : term226 A B _93258 R x t) (h4 : @IN A x s) : (term226 A B _93258 R x t) = False.
Proof. exact (prop_ext (fun h5 : term226 A B _93258 R x t => @lem6997234 A B _93258 R t x s h1 h2 h3 h4) (fun h5 : False => @lem6995406 A B _93258 R x t h3)). Qed.
Lemma lem6997236 {A B : Type'} (_93258 : type830 A B) (R : type1413 A B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : term174 A B _93258) (h3 : term226 A B _93258 R x t) (h4 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem6997235 A B _93258 R t x s h1 h2 h3 h4) (@lem6995406 A B _93258 R x t h3)). Qed.
Lemma lem6997237 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_93258 : type830 A B) (x : A) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : term174 A B _93258) (h3 : @IN A x s) : term225 A B _93258 R x t.
Proof. exact (fun h0 : term226 A B _93258 R x t => @lem6997236 A B _93258 R t x s h1 h2 h0 h3). Qed.
Lemma lem6997238 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_93258 : type830 A B) (x : A) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : term174 A B _93258) (h3 : @IN A x s) : term157 A B _93258 R x t.
Proof. exact (EQ_MP (@lem6995405 A B _93258 R x t) (@lem6997237 A B t R _93258 x s h1 h2 h3)). Qed.
Lemma lem6997239 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_93258 : type830 A B) (h1 : term34 A B s t R) (h2 : term174 A B _93258) : term177 A B s _93258 R x t.
Proof. exact (fun h0 : @IN A x s => @lem6997238 A B t R _93258 x s h1 h2 h0). Qed.
Lemma lem6997244 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_93258 : type830 A B) (h1 : term34 A B s t R) (h2 : term174 A B _93258) : term179 A B s _93258 R t.
Proof. exact (fun x : A => @lem6997239 A B x s t R _93258 h1 h2). Qed.
Lemma lem6997245 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_93258 : type830 A B) (h1 : term174 A B _93258) : term204 A B s _93258 R t.
Proof. exact (fun h0 : term34 A B s t R => @lem6997244 A B s t R _93258 h0 h1). Qed.
Lemma lem6997246 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (_93258 : type830 A B) (h1 : term174 A B _93258) : term205 A B s _93258 R t.
Proof. exact (fun h0 : @FINITE A s => @lem6997245 A B s R t _93258 h1). Qed.
Lemma lem6997247 {A B : Type'} (s : A -> Prop) (_93258 : type830 A B) (R : type1413 A B) (t : B -> Prop) : term206 A B s _93258 R t.
Proof. exact (fun h0 : term174 A B _93258 => @lem6997246 A B s R t _93258 h0). Qed.
Lemma lem6997252 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term209 A B s R t.
Proof. exact (fun _93258 : type830 A B => @lem6997247 A B s _93258 R t). Qed.
Lemma lem6997257 {A B : Type'} (R : type1413 A B) (t : B -> Prop) : term213 A B R t.
Proof. exact (fun s : A -> Prop => @lem6997252 A B s R t). Qed.
Lemma lem6997262 {A B : Type'} (t : B -> Prop) : term217 A B t.
Proof. exact (fun R : type1413 A B => @lem6997257 A B R t). Qed.
Lemma lem6997267 {A B : Type'} : term221 A B.
Proof. exact (fun t : B -> Prop => @lem6997262 A B t). Qed.
Lemma lem6997268 {A B : Type'} : term220 A B.
Proof. exact (EQ_MP (@lem6995397 A B) (@lem6997267 A B)). Qed.
Lemma lem6997269 {A B : Type'} (t : B -> Prop) : term597 A B t.
Proof. exact (@lem6997268 A B t). Qed.
Lemma lem6997270 {A B : Type'} (t : B -> Prop) : (term597 A B t) = (term216 A B t).
Proof. exact (eq_refl (term597 A B t)). Qed.
Lemma lem6997271 {A B : Type'} (t : B -> Prop) : term216 A B t.
Proof. exact (EQ_MP (@lem6997270 A B t) (@lem6997269 A B t)). Qed.
Lemma lem6997272 {A B : Type'} (t : B -> Prop) (R : type1413 A B) : term598 A B t R.
Proof. exact (@lem6997271 A B t R). Qed.
Lemma lem6997273 {A B : Type'} (R : type1413 A B) (t : B -> Prop) : (term598 A B t R) = (term212 A B R t).
Proof. exact (eq_refl (term598 A B t R)). Qed.
Lemma lem6997274 {A B : Type'} (R : type1413 A B) (t : B -> Prop) : term212 A B R t.
Proof. exact (EQ_MP (@lem6997273 A B R t) (@lem6997272 A B t R)). Qed.
Lemma lem6997275 {A B : Type'} (R : type1413 A B) (t : B -> Prop) (s : A -> Prop) : term599 A B R t s.
Proof. exact (@lem6997274 A B R t s). Qed.
Lemma lem6997276 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term599 A B R t s) = (term190 A B s R t).
Proof. exact (eq_refl (term599 A B R t s)). Qed.
Lemma lem6997277 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term190 A B s R t.
Proof. exact (EQ_MP (@lem6997276 A B s R t) (@lem6997275 A B R t s)). Qed.
Lemma lem6997279 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term141 A B s R t.
Proof. exact (@lem6995136 A B s R t (@lem6997277 A B s R t)). Qed.
Lemma lem6997280 {A B : Type'} (R : type1413 A B) (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : term185 A B s R t.
Proof. exact (@lem6997279 A B s R t (@lem6994798 A s h1)). Qed.
Lemma lem6997281 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : term121 A B s R t.
Proof. exact (@lem6997280 A B R t s h2 (@lem6994797 A B s t R h1)). Qed.
Lemma lem6997282 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) (h3 : term122 A B s R t) : False.
Proof. exact (@lem6997281 A B t R s h1 h2 (@lem6994992 A B s R t h3)). Qed.
Lemma lem6997283 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) (h3 : term122 A B s R t) : (term122 A B s R t) = False.
Proof. exact (prop_ext (fun h4 : term122 A B s R t => @lem6997282 A B s R t h1 h2 h3) (fun h4 : False => @lem6994992 A B s R t h3)). Qed.
Lemma lem6997284 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) (h3 : term122 A B s R t) : False.
Proof. exact (EQ_MP (@lem6997283 A B s R t h1 h2 h3) (@lem6994992 A B s R t h3)). Qed.
Lemma lem6997285 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : term121 A B s R t.
Proof. exact (fun h0 : term122 A B s R t => @lem6997284 A B s R t h1 h2 h0). Qed.
Lemma lem6997286 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : term81 A B s R t.
Proof. exact (EQ_MP (@lem6994991 A B s R t) (@lem6997285 A B t R s h1 h2)). Qed.
Lemma lem6997287 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> nat) (h1 : (term109 A B s t R g) = (@nsum A s g)) : (term109 A B s t R g) = (@nsum A s g).
Proof. exact (h1). Qed.
Lemma lem6997288 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> nat) (h1 : (term109 A B s t R g) = (@nsum A s g)) : (@nsum A s g) = (term109 A B s t R g).
Proof. exact (SYM (@lem6997287 A B t R s g h1)). Qed.
Lemma lem6997289 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (g : A -> nat) : (term600 A B t s R g) = (term600 A B t s R g).
Proof. exact (eq_refl (term600 A B t s R g)). Qed.
Lemma lem6997290 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> nat) (h1 : (term109 A B s t R g) = (@nsum A s g)) : (term601 A B t R s g) = (term602 A B s t R g).
Proof. exact (MK_COMB (@lem6997289 A B t s R g) (@lem6997288 A B t R s g h1)). Qed.
Lemma lem6997291 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (g : A -> nat) : (term602 A B s t R g) = ((term115 A B t s R g) = (term109 A B s t R g)).
Proof. exact (eq_refl (term602 A B s t R g)). Qed.
Lemma lem6997292 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> nat) : (term603 A B t R s g) = (term603 A B t R s g).
Proof. exact (eq_refl (term603 A B t R s g)). Qed.
Lemma lem6997293 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (g : A -> nat) : ((term601 A B t R s g) = (term602 A B s t R g)) = ((term601 A B t R s g) = ((term115 A B t s R g) = (term109 A B s t R g))).
Proof. exact (MK_COMB (@lem6997292 A B t R s g) (@lem6997291 A B s t R g)). Qed.
Lemma lem6997294 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> nat) : (term601 A B t R s g) = ((term115 A B t s R g) = (@nsum A s g)).
Proof. exact (eq_refl (term601 A B t R s g)). Qed.
Lemma lem6997295 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6997296 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> nat) : (term603 A B t R s g) = (term604 A B t R s g).
Proof. exact (MK_COMB (@lem6997295) (@lem6997294 A B t R s g)). Qed.
Lemma lem6997297 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (g : A -> nat) : ((term115 A B t s R g) = (term109 A B s t R g)) = ((term115 A B t s R g) = (term109 A B s t R g)).
Proof. exact (eq_refl ((term115 A B t s R g) = (term109 A B s t R g))). Qed.
Lemma lem6997298 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (g : A -> nat) : ((term601 A B t R s g) = ((term115 A B t s R g) = (term109 A B s t R g))) = (((term115 A B t s R g) = (@nsum A s g)) = ((term115 A B t s R g) = (term109 A B s t R g))).
Proof. exact (MK_COMB (@lem6997296 A B t R s g) (@lem6997297 A B s t R g)). Qed.
Lemma lem6997299 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (g : A -> nat) : ((term601 A B t R s g) = (term602 A B s t R g)) = (((term115 A B t s R g) = (@nsum A s g)) = ((term115 A B t s R g) = (term109 A B s t R g))).
Proof. exact (TRANS (@lem6997293 A B s t R g) (@lem6997298 A B s t R g)). Qed.
Lemma lem6997300 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> nat) (h1 : (term109 A B s t R g) = (@nsum A s g)) : ((term115 A B t s R g) = (@nsum A s g)) = ((term115 A B t s R g) = (term109 A B s t R g)).
Proof. exact (EQ_MP (@lem6997299 A B s t R g) (@lem6997290 A B t R s g h1)). Qed.
Lemma lem6997301 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> nat) (h1 : (term109 A B s t R g) = (@nsum A s g)) : ((term115 A B t s R g) = (term109 A B s t R g)) = ((term115 A B t s R g) = (@nsum A s g)).
Proof. exact (SYM (@lem6997300 A B t R s g h1)). Qed.
Lemma lem6997303 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : term6 _127166 f s g.
Proof. exact (EQ_MP (@lem6994771 _127166 f s g) (@lem6994770 _127166 f s g)). Qed.
Lemma lem6997304 {B : Type'} (f : B -> nat) (s : B -> Prop) (g : B -> nat) : term6 B f s g.
Proof. exact (@lem6997303 B f s g). Qed.
Lemma lem6997305 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (g : A -> nat) : term605 A B s t R g.
Proof. exact (@lem6997304 B (term606 A B s R g) t (term107 A B s t R g)). Qed.
Lemma lem6997306 {B : Type'} (x : B) (t : B -> Prop) (h1 : @IN B x t) : @IN B x t.
Proof. exact (h1). Qed.
Lemma lem6997310 {A B : Type'} (f : A -> B) (y : A) : (term69 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6997311 {B : Type'} (f : B -> nat) (y : B) : (term607 B f y) = (f y).
Proof. exact (@lem6997310 B nat f y). Qed.
Lemma lem6997312 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (g : A -> nat) (x : B) : (term608 A B s R g x) = (term609 A B s R g x).
Proof. exact (@lem6997311 B (term606 A B s R g) x). Qed.
Lemma lem6997313 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (y : B) (g : A -> nat) : (term609 A B s R g y) = (term610 A B s R y g).
Proof. exact (eq_refl (term609 A B s R g y)). Qed.
Lemma lem6997314 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (g : A -> nat) : (term611 A B s R g) = (term606 A B s R g).
Proof. exact (fun_ext (fun y : B => @lem6997313 A B s R y g)). Qed.
Lemma lem6997315 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6997316 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (g : A -> nat) (x : B) : (term608 A B s R g x) = (term609 A B s R g x).
Proof. exact (MK_COMB (@lem6997314 A B s R g) (@lem6997315 B x)). Qed.
Lemma lem6997317 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6997318 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (g : A -> nat) (x : B) : (term612 A B s R g x) = (term613 A B s R g x).
Proof. exact (MK_COMB (@lem6997317) (@lem6997316 A B s R g x)). Qed.
Lemma lem6997319 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) (g : A -> nat) : (term609 A B s R g x) = (term610 A B s R x g).
Proof. exact (eq_refl (term609 A B s R g x)). Qed.
Lemma lem6997320 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) (g : A -> nat) : ((term608 A B s R g x) = (term609 A B s R g x)) = ((term609 A B s R g x) = (term610 A B s R x g)).
Proof. exact (MK_COMB (@lem6997318 A B s R g x) (@lem6997319 A B s R x g)). Qed.
Lemma lem6997321 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) (g : A -> nat) : (term609 A B s R g x) = (term610 A B s R x g).
Proof. exact (EQ_MP (@lem6997320 A B s R x g) (@lem6997312 A B s R g x)). Qed.
Lemma lem6997328 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6997329 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) (g : A -> nat) : (term613 A B s R g x) = (term614 A B s R x g).
Proof. exact (MK_COMB (@lem6997328) (@lem6997321 A B s R x g)). Qed.
Lemma lem6997331 {A B : Type'} (f : A -> B) (y : A) : (term69 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6997332 {B : Type'} (f : B -> nat) (y : B) : (term607 B f y) = (f y).
Proof. exact (@lem6997331 B nat f y). Qed.
Lemma lem6997333 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (g : A -> nat) (x : B) : (term615 A B s t R g x) = (term616 A B s t R g x).
Proof. exact (@lem6997332 B (term107 A B s t R g) x). Qed.
Lemma lem6997334 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (y : B) (g : A -> nat) : (term616 A B s t R g y) = (term105 A B s t R y g).
Proof. exact (eq_refl (term616 A B s t R g y)). Qed.
Lemma lem6997335 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (g : A -> nat) : (term617 A B s t R g) = (term107 A B s t R g).
Proof. exact (fun_ext (fun y : B => @lem6997334 A B s t R y g)). Qed.
Lemma lem6997336 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6997337 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (g : A -> nat) (x : B) : (term615 A B s t R g x) = (term616 A B s t R g x).
Proof. exact (MK_COMB (@lem6997335 A B s t R g) (@lem6997336 B x)). Qed.
Lemma lem6997338 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6997339 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (g : A -> nat) (x : B) : (term618 A B s t R g x) = (term619 A B s t R g x).
Proof. exact (MK_COMB (@lem6997338) (@lem6997337 A B s t R g x)). Qed.
Lemma lem6997340 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (g : A -> nat) : (term616 A B s t R g x) = (term105 A B s t R x g).
Proof. exact (eq_refl (term616 A B s t R g x)). Qed.
Lemma lem6997341 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (g : A -> nat) : ((term615 A B s t R g x) = (term616 A B s t R g x)) = ((term616 A B s t R g x) = (term105 A B s t R x g)).
Proof. exact (MK_COMB (@lem6997339 A B s t R g x) (@lem6997340 A B s t R x g)). Qed.
Lemma lem6997342 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (g : A -> nat) : (term616 A B s t R g x) = (term105 A B s t R x g).
Proof. exact (EQ_MP (@lem6997341 A B s t R x g) (@lem6997333 A B s t R g x)). Qed.
Lemma lem6997353 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (g : A -> nat) : ((term609 A B s R g x) = (term616 A B s t R g x)) = ((term610 A B s R x g) = (term105 A B s t R x g)).
Proof. exact (MK_COMB (@lem6997329 A B s R x g) (@lem6997342 A B s t R x g)). Qed.
Lemma lem6997356 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (g : A -> nat) (x : B) : ((term610 A B s R x g) = (term105 A B s t R x g)) = ((term609 A B s R g x) = (term616 A B s t R g x)).
Proof. exact (SYM (@lem6997353 A B s t R x g)). Qed.
Lemma lem6997357 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6997358 {A : Type'} : (@nsum A) = (@nsum A).
Proof. exact (eq_refl (@nsum A)). Qed.
Lemma lem6997359 (t1 : Prop) : term16 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem6997360 (t1 : Prop) : (term16 t1) = (term17 t1).
Proof. exact (eq_refl (term16 t1)). Qed.
Lemma lem6997361 (t1 : Prop) : term17 t1.
Proof. exact (EQ_MP (@lem6997360 t1) (@lem6997359 t1)). Qed.
Lemma lem6997362 (t1 : Prop) (t2 : Prop) : term18 t1 t2.
Proof. exact (@lem6997361 t1 t2). Qed.
Lemma lem6997363 (t1 : Prop) (t2 : Prop) : (term18 t1 t2) = (term19 t1 t2).
Proof. exact (eq_refl (term18 t1 t2)). Qed.
Lemma lem6997364 (t1 : Prop) (t2 : Prop) : term19 t1 t2.
Proof. exact (EQ_MP (@lem6997363 t1 t2) (@lem6997362 t1 t2)). Qed.
Lemma lem6997365 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term20 t1 t2 t3.
Proof. exact (@lem6997364 t1 t2 t3). Qed.
Lemma lem6997366 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term20 t1 t2 t3) = ((term21 t1 t2 t3) = (term22 t1 t2 t3)).
Proof. exact (eq_refl (term20 t1 t2 t3)). Qed.
Lemma lem6997367 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term21 t1 t2 t3) = (term22 t1 t2 t3).
Proof. exact (EQ_MP (@lem6997366 t1 t2 t3) (@lem6997365 t1 t2 t3)). Qed.
Lemma lem6997368 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term22 t1 t2 t3) = (term21 t1 t2 t3).
Proof. exact (SYM (@lem6997367 t1 t2 t3)). Qed.
Lemma lem6997369 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : term620 A B t R s.
Proof. exact (conj (@lem6994797 A B s t R h1) (@lem6994798 A s h2)). Qed.
Lemma lem6997370 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (x : B) (t : B -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) (h3 : @IN B x t) : term621 A B x t R s.
Proof. exact (conj (@lem6997306 B x t h3) (@lem6997369 A B t R s h1 h2)). Qed.
Lemma lem6997388 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term622 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem6997389 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term622 A s t).
Proof. exact (@lem6997388 A s t). Qed.
Lemma lem6997390 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : ((term623 A B s R x) = (term101 A B s t R x)) = (term624 A B s t R x).
Proof. exact (@lem6997389 A (term623 A B s R x) (term101 A B s t R x)). Qed.
Lemma lem6997417 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term625 A B x t R s) = (term625 A B x t R s).
Proof. exact (eq_refl (term625 A B x t R s)). Qed.
Lemma lem6997418 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term626 A B s t R x) = (term627 A B s t R x).
Proof. exact (MK_COMB (@lem6997417 A B x t R s) (@lem6997390 A B s t R x)). Qed.
Lemma lem6997421 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term627 A B s t R x) = (term626 A B s t R x).
Proof. exact (SYM (@lem6997418 A B s t R x)). Qed.
Lemma lem6997427 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6997428 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem6997427 B P x). Qed.
Lemma lem6997429 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem6997428 B t x). Qed.
Lemma lem6997430 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6997431 {B : Type'} (t : B -> Prop) (x : B) : (term87 B x t) = (term628 B t x).
Proof. exact (MK_COMB (@lem6997430) (@lem6997429 B t x)). Qed.
Lemma lem6997441 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6997442 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem6997441 A P x). Qed.
Lemma lem6997443 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem6997442 A s x). Qed.
Lemma lem6997444 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6997445 {A : Type'} (s : A -> Prop) (x : A) : (term63 A x s) = (term629 A s x).
Proof. exact (MK_COMB (@lem6997444) (@lem6997443 A s x)). Qed.
Lemma lem6997449 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6997450 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem6997449 B P x). Qed.
Lemma lem6997451 {B : Type'} (t : B -> Prop) (y : B) : (@IN B y t) = (t y).
Proof. exact (@lem6997450 B t y). Qed.
Lemma lem6997452 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6997453 {B : Type'} (t : B -> Prop) (y : B) : (term87 B y t) = (term628 B t y).
Proof. exact (MK_COMB (@lem6997452) (@lem6997451 B t y)). Qed.
Lemma lem6997454 {A B : Type'} (R : type1413 A B) (x : A) (y : B) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem6997455 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term129 A B t R x y) = (term630 A B t R x y).
Proof. exact (MK_COMB (@lem6997453 B t y) (@lem6997454 A B R x y)). Qed.
Lemma lem6997458 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term125 A B t R x) = (term631 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem6997455 A B t R x y)). Qed.
Lemma lem6997459 {B : Type'} : (@ex1 B) = (@ex1 B).
Proof. exact (eq_refl (@ex1 B)). Qed.
Lemma lem6997460 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term222 A B t R x) = (term632 A B t R x).
Proof. exact (MK_COMB (@lem6997459 B) (@lem6997458 A B t R x)). Qed.
Lemma lem6997461 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term223 A B s t R x) = (term633 A B s t R x).
Proof. exact (MK_COMB (@lem6997445 A s x) (@lem6997460 A B t R x)). Qed.
Lemma lem6997464 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term224 A B s t R) = (term634 A B s t R).
Proof. exact (fun_ext (fun x : A => @lem6997461 A B s t R x)). Qed.
Lemma lem6997465 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6997466 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term34 A B s t R) = (term635 A B s t R).
Proof. exact (MK_COMB (@lem6997465 A) (@lem6997464 A B s t R)). Qed.
Lemma lem6997471 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6997472 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term636 A B s t R) = (term637 A B s t R).
Proof. exact (MK_COMB (@lem6997471) (@lem6997466 A B s t R)). Qed.
Lemma lem6997473 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem6997474 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term620 A B t R s) = (term638 A B t R s).
Proof. exact (MK_COMB (@lem6997472 A B s t R) (@lem6997473 A s)). Qed.
Lemma lem6997477 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term621 A B x t R s) = (term639 A B x t R s).
Proof. exact (MK_COMB (@lem6997431 B t x) (@lem6997474 A B t R s)). Qed.
Lemma lem6997480 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6997481 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term625 A B x t R s) = (term640 A B x t R s).
Proof. exact (MK_COMB (@lem6997480) (@lem6997477 A B x t R s)). Qed.
Lemma lem6997489 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term641 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem6997490 {A : Type'} (p : A -> Prop) (x : A) : (term641 A x p) = (p x).
Proof. exact (@lem6997489 A p x). Qed.
Lemma lem6997491 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) (x' : A) : (term642 A B x' s R x) = (term643 A B s R x x').
Proof. exact (@lem6997490 A (term644 A B s R x) x'). Qed.
Lemma lem6997492 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term643 A B s R x' x) = (term645 A B s R x x').
Proof. exact (eq_refl (term643 A B s R x' x)). Qed.
Lemma lem6997493 {A : Type'} (GEN_PVAR_297 : A) : (@SETSPEC A GEN_PVAR_297) = (@SETSPEC A GEN_PVAR_297).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_297)). Qed.
Lemma lem6997494 {A B : Type'} (GEN_PVAR_297 : A) (s : A -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term646 A B GEN_PVAR_297 s R x' x) = (term647 A B GEN_PVAR_297 s R x x').
Proof. exact (MK_COMB (@lem6997493 A GEN_PVAR_297) (@lem6997492 A B s R x x')). Qed.
Lemma lem6997495 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6997496 {A B : Type'} (GEN_PVAR_297 : A) (s : A -> Prop) (R : type1413 A B) (x : B) (x' : A) : (term648 A B GEN_PVAR_297 s R x x') = (term649 A B GEN_PVAR_297 s R x x').
Proof. exact (MK_COMB (@lem6997494 A B GEN_PVAR_297 s R x' x) (@lem6997495 A x')). Qed.
Lemma lem6997497 {A B : Type'} (GEN_PVAR_297 : A) (s : A -> Prop) (R : type1413 A B) (x : B) : (term650 A B GEN_PVAR_297 s R x) = (term651 A B GEN_PVAR_297 s R x).
Proof. exact (fun_ext (fun x' : A => @lem6997496 A B GEN_PVAR_297 s R x x')). Qed.
Lemma lem6997498 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6997499 {A B : Type'} (GEN_PVAR_297 : A) (s : A -> Prop) (R : type1413 A B) (x : B) : (term652 A B GEN_PVAR_297 s R x) = (term653 A B GEN_PVAR_297 s R x).
Proof. exact (MK_COMB (@lem6997498 A) (@lem6997497 A B GEN_PVAR_297 s R x)). Qed.
Lemma lem6997500 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : (term654 A B s R x) = (term655 A B s R x).
Proof. exact (fun_ext (fun GEN_PVAR_297 : A => @lem6997499 A B GEN_PVAR_297 s R x)). Qed.
Lemma lem6997501 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6997502 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : (term656 A B s R x) = (term623 A B s R x).
Proof. exact (MK_COMB (@lem6997501 A) (@lem6997500 A B s R x)). Qed.
Lemma lem6997503 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6997504 {A B : Type'} (x : A) (s : A -> Prop) (R : type1413 A B) (x' : B) : (term642 A B x s R x') = (term657 A B x s R x').
Proof. exact (MK_COMB (@lem6997503 A x) (@lem6997502 A B s R x')). Qed.
Lemma lem6997505 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6997506 {A B : Type'} (x : A) (s : A -> Prop) (R : type1413 A B) (x' : B) : (term658 A B x s R x') = (term659 A B x s R x').
Proof. exact (MK_COMB (@lem6997505) (@lem6997504 A B x s R x')). Qed.
Lemma lem6997507 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term643 A B s R x' x) = (term645 A B s R x x').
Proof. exact (eq_refl (term643 A B s R x' x)). Qed.
Lemma lem6997508 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : A) (x' : B) : ((term642 A B x s R x') = (term643 A B s R x' x)) = ((term657 A B x s R x') = (term645 A B s R x x')).
Proof. exact (MK_COMB (@lem6997506 A B x s R x') (@lem6997507 A B s R x x')). Qed.
Lemma lem6997509 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term657 A B x s R x') = (term645 A B s R x x').
Proof. exact (EQ_MP (@lem6997508 A B s R x x') (@lem6997491 A B s R x' x)). Qed.
Lemma lem6997513 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6997514 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem6997513 A P x). Qed.
Lemma lem6997515 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem6997514 A s x). Qed.
Lemma lem6997516 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6997517 {A : Type'} (s : A -> Prop) (x : A) : (term87 A x s) = (term628 A s x).
Proof. exact (MK_COMB (@lem6997516) (@lem6997515 A s x)). Qed.
Lemma lem6997518 {A B : Type'} (R : type1413 A B) (x : A) (x' : B) : (R x x') = (R x x').
Proof. exact (eq_refl (R x x')). Qed.
Lemma lem6997519 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term645 A B s R x x') = (term660 A B s R x x').
Proof. exact (MK_COMB (@lem6997517 A s x) (@lem6997518 A B R x x')). Qed.
Lemma lem6997522 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term657 A B x s R x') = (term660 A B s R x x').
Proof. exact (TRANS (@lem6997509 A B s R x x') (@lem6997519 A B s R x x')). Qed.
Lemma lem6997523 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6997524 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term659 A B x s R x') = (term661 A B s R x x').
Proof. exact (MK_COMB (@lem6997523) (@lem6997522 A B s R x x')). Qed.
Lemma lem6997526 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term641 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem6997527 {A : Type'} (p : A -> Prop) (x : A) : (term641 A x p) = (p x).
Proof. exact (@lem6997526 A p x). Qed.
Lemma lem6997528 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (x' : A) : (term662 A B x' s t R x) = (term663 A B s t R x x').
Proof. exact (@lem6997527 A (term664 A B s t R x) x'). Qed.
Lemma lem6997529 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term663 A B s t R x' x) = (term89 A B s t R x x').
Proof. exact (eq_refl (term663 A B s t R x' x)). Qed.
Lemma lem6997530 {A : Type'} (GEN_PVAR_296 : A) : (@SETSPEC A GEN_PVAR_296) = (@SETSPEC A GEN_PVAR_296).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_296)). Qed.
Lemma lem6997531 {A B : Type'} (GEN_PVAR_296 : A) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term665 A B GEN_PVAR_296 s t R x' x) = (term91 A B GEN_PVAR_296 s t R x x').
Proof. exact (MK_COMB (@lem6997530 A GEN_PVAR_296) (@lem6997529 A B s t R x x')). Qed.
Lemma lem6997532 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6997533 {A B : Type'} (GEN_PVAR_296 : A) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (x' : A) : (term666 A B GEN_PVAR_296 s t R x x') = (term93 A B GEN_PVAR_296 s t R x x').
Proof. exact (MK_COMB (@lem6997531 A B GEN_PVAR_296 s t R x' x) (@lem6997532 A x')). Qed.
Lemma lem6997534 {A B : Type'} (GEN_PVAR_296 : A) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term667 A B GEN_PVAR_296 s t R x) = (term95 A B GEN_PVAR_296 s t R x).
Proof. exact (fun_ext (fun x' : A => @lem6997533 A B GEN_PVAR_296 s t R x x')). Qed.
Lemma lem6997535 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6997536 {A B : Type'} (GEN_PVAR_296 : A) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term668 A B GEN_PVAR_296 s t R x) = (term97 A B GEN_PVAR_296 s t R x).
Proof. exact (MK_COMB (@lem6997535 A) (@lem6997534 A B GEN_PVAR_296 s t R x)). Qed.
Lemma lem6997537 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term669 A B s t R x) = (term99 A B s t R x).
Proof. exact (fun_ext (fun GEN_PVAR_296 : A => @lem6997536 A B GEN_PVAR_296 s t R x)). Qed.
Lemma lem6997538 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6997539 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term670 A B s t R x) = (term101 A B s t R x).
Proof. exact (MK_COMB (@lem6997538 A) (@lem6997537 A B s t R x)). Qed.
Lemma lem6997540 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6997541 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x' : B) : (term662 A B x s t R x') = (term671 A B x s t R x').
Proof. exact (MK_COMB (@lem6997540 A x) (@lem6997539 A B s t R x')). Qed.
Lemma lem6997542 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6997543 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x' : B) : (term672 A B x s t R x') = (term673 A B x s t R x').
Proof. exact (MK_COMB (@lem6997542) (@lem6997541 A B x s t R x')). Qed.
Lemma lem6997544 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term663 A B s t R x' x) = (term89 A B s t R x x').
Proof. exact (eq_refl (term663 A B s t R x' x)). Qed.
Lemma lem6997545 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : ((term662 A B x s t R x') = (term663 A B s t R x' x)) = ((term671 A B x s t R x') = (term89 A B s t R x x')).
Proof. exact (MK_COMB (@lem6997543 A B x s t R x') (@lem6997544 A B s t R x x')). Qed.
Lemma lem6997546 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term671 A B x s t R x') = (term89 A B s t R x x').
Proof. exact (EQ_MP (@lem6997545 A B s t R x x') (@lem6997528 A B s t R x' x)). Qed.
Lemma lem6997550 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6997551 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem6997550 A P x). Qed.
Lemma lem6997552 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem6997551 A s x). Qed.
Lemma lem6997553 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6997554 {A : Type'} (s : A -> Prop) (x : A) : (term87 A x s) = (term628 A s x).
Proof. exact (MK_COMB (@lem6997553) (@lem6997552 A s x)). Qed.
Lemma lem6997560 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6997561 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem6997560 B P x). Qed.
Lemma lem6997562 {B : Type'} (t : B -> Prop) (y : B) : (@IN B y t) = (t y).
Proof. exact (@lem6997561 B t y). Qed.
Lemma lem6997563 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6997564 {B : Type'} (t : B -> Prop) (y : B) : (term87 B y t) = (term628 B t y).
Proof. exact (MK_COMB (@lem6997563) (@lem6997562 B t y)). Qed.
Lemma lem6997565 {A B : Type'} (R : type1413 A B) (x : A) (y : B) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem6997566 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term129 A B t R x y) = (term630 A B t R x y).
Proof. exact (MK_COMB (@lem6997564 B t y) (@lem6997565 A B R x y)). Qed.
Lemma lem6997569 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term125 A B t R x) = (term631 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem6997566 A B t R x y)). Qed.
Lemma lem6997570 {B : Type'} : (@ε B) = (@ε B).
Proof. exact (eq_refl (@ε B)). Qed.
Lemma lem6997571 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term72 A B t R x) = (term674 A B t R x).
Proof. exact (MK_COMB (@lem6997570 B) (@lem6997569 A B t R x)). Qed.
Lemma lem6997572 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6997573 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term86 A B t R x) = (term675 A B t R x).
Proof. exact (MK_COMB (@lem6997572 B) (@lem6997571 A B t R x)). Qed.
Lemma lem6997574 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6997575 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : ((term72 A B t R x) = x') = ((term674 A B t R x) = x').
Proof. exact (MK_COMB (@lem6997573 A B t R x) (@lem6997574 B x')). Qed.
Lemma lem6997578 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term89 A B s t R x x') = (term676 A B s t R x x').
Proof. exact (MK_COMB (@lem6997554 A s x) (@lem6997575 A B t R x x')). Qed.
Lemma lem6997581 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term671 A B x s t R x') = (term676 A B s t R x x').
Proof. exact (TRANS (@lem6997546 A B s t R x x') (@lem6997578 A B s t R x x')). Qed.
Lemma lem6997582 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : ((term657 A B x s R x') = (term671 A B x s t R x')) = ((term660 A B s R x x') = (term676 A B s t R x x')).
Proof. exact (MK_COMB (@lem6997524 A B s R x x') (@lem6997581 A B s t R x x')). Qed.
Lemma lem6997585 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term677 A B s t R x) = (term678 A B s t R x).
Proof. exact (fun_ext (fun x' : A => @lem6997582 A B s t R x' x)). Qed.
Lemma lem6997586 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6997587 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term624 A B s t R x) = (term679 A B s t R x).
Proof. exact (MK_COMB (@lem6997586 A) (@lem6997585 A B s t R x)). Qed.
Lemma lem6997592 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term627 A B s t R x) = (term680 A B s t R x).
Proof. exact (MK_COMB (@lem6997481 A B x t R s) (@lem6997587 A B s t R x)). Qed.
Lemma lem6997595 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term680 A B s t R x) = (term627 A B s t R x).
Proof. exact (SYM (@lem6997592 A B s t R x)). Qed.
Lemma lem6997597 (p : Prop) : p = (term120 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6997598 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term680 A B s t R x) = (term681 A B s t R x).
Proof. exact (@lem6997597 (term680 A B s t R x)). Qed.
Lemma lem6997599 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term681 A B s t R x) = (term680 A B s t R x).
Proof. exact (SYM (@lem6997598 A B s t R x)). Qed.
Lemma lem6997600 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term682 A B s t R x) : term682 A B s t R x.
Proof. exact (h1). Qed.
Lemma lem6997623 {B : Type'} (P : B -> Prop) : term123 B P.
Proof. exact (@lem19732 B P). Qed.
Lemma lem6997624 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : term683 A B t R x.
Proof. exact (@lem6997623 B (term631 A B t R x)). Qed.
Lemma lem6997625 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term684 A B t R x) = (term685 A B t R x).
Proof. exact (eq_refl (term684 A B t R x)). Qed.
Lemma lem6997626 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term686 A B t R x x') = (term630 A B t R x x').
Proof. exact (eq_refl (term686 A B t R x x')). Qed.
Lemma lem6997627 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6997628 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term687 A B t R x x') = (term688 A B t R x x').
Proof. exact (MK_COMB (@lem6997627) (@lem6997626 A B t R x x')). Qed.
Lemma lem6997629 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term689 A B x t R x') = (term690 A B x t R x').
Proof. exact (MK_COMB (@lem6997628 A B t R x' x) (@lem6997625 A B t R x')). Qed.
Lemma lem6997630 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term691 A B t R x) = (term692 A B t R x).
Proof. exact (fun_ext (fun x' : B => @lem6997629 A B x' t R x)). Qed.
Lemma lem6997631 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6997632 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term683 A B t R x) = (term693 A B t R x).
Proof. exact (MK_COMB (@lem6997631 B) (@lem6997630 A B t R x)). Qed.
Lemma lem6997633 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : term693 A B t R x.
Proof. exact (EQ_MP (@lem6997632 A B t R x) (@lem6997624 A B t R x)). Qed.
Lemma lem6997634 {A B : Type'} (t : B -> Prop) (R : type1413 A B) : term694 A B t R.
Proof. exact (fun x : A => @lem6997633 A B t R x). Qed.
Lemma lem6997635 {A B : Type'} (t : B -> Prop) : term695 A B t.
Proof. exact (fun R : type1413 A B => @lem6997634 A B t R). Qed.
Lemma lem6997636 {A B : Type'} : term696 A B.
Proof. exact (fun t : B -> Prop => @lem6997635 A B t). Qed.
Lemma lem6997637 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term697 A B s t R x) : term697 A B s t R x.
Proof. exact (h1). Qed.
Lemma lem6997638 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term697 A B s t R x) : term681 A B s t R x.
Proof. exact (@lem6997637 A B s t R x h1 (@lem6997636 A B)). Qed.
Lemma lem6997639 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term698 A B s t R x.
Proof. exact (fun h0 : term697 A B s t R x => @lem6997638 A B s t R x h0). Qed.
Lemma lem6997640 {A B : Type'} (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : _93304 = (term699 A B).
Proof. exact (h1). Qed.
Lemma lem6997641 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem6997642 {A B : Type'} (t : B -> Prop) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (_93304 t) = (term700 A B t).
Proof. exact (MK_COMB (@lem6997640 A B _93304 h1) (@lem6997641 B t)). Qed.
Lemma lem6997643 {A B : Type'} (t : B -> Prop) : (term700 A B t) = (term701 A B t).
Proof. exact (eq_refl (term700 A B t)). Qed.
Lemma lem6997644 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) : (term146 A B _93304 t) = (term146 A B _93304 t).
Proof. exact (eq_refl (term146 A B _93304 t)). Qed.
Lemma lem6997645 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) : ((_93304 t) = (term700 A B t)) = ((_93304 t) = (term701 A B t)).
Proof. exact (MK_COMB (@lem6997644 A B _93304 t) (@lem6997643 A B t)). Qed.
Lemma lem6997646 {A B : Type'} (t : B -> Prop) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (_93304 t) = (term701 A B t).
Proof. exact (EQ_MP (@lem6997645 A B _93304 t) (@lem6997642 A B t _93304 h1)). Qed.
Lemma lem6997647 {A B : Type'} (R : type1413 A B) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem6997648 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (_93304 t R) = (term702 A B t R).
Proof. exact (MK_COMB (@lem6997646 A B t _93304 h1) (@lem6997647 A B R)). Qed.
Lemma lem6997649 {A B : Type'} (t : B -> Prop) (R : type1413 A B) : (term702 A B t R) = (term703 A B t R).
Proof. exact (eq_refl (term702 A B t R)). Qed.
Lemma lem6997650 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term148 A B _93304 t R) = (term148 A B _93304 t R).
Proof. exact (eq_refl (term148 A B _93304 t R)). Qed.
Lemma lem6997651 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : ((_93304 t R) = (term702 A B t R)) = ((_93304 t R) = (term703 A B t R)).
Proof. exact (MK_COMB (@lem6997650 A B _93304 t R) (@lem6997649 A B t R)). Qed.
Lemma lem6997652 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (_93304 t R) = (term703 A B t R).
Proof. exact (EQ_MP (@lem6997651 A B _93304 t R) (@lem6997648 A B t R _93304 h1)). Qed.
Lemma lem6997653 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6997654 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (_93304 t R x) = (term704 A B t R x).
Proof. exact (MK_COMB (@lem6997652 A B t R _93304 h1) (@lem6997653 A x)). Qed.
Lemma lem6997655 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term704 A B t R x) = (term674 A B t R x).
Proof. exact (eq_refl (term704 A B t R x)). Qed.
Lemma lem6997656 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term149 A B _93304 t R x) = (term149 A B _93304 t R x).
Proof. exact (eq_refl (term149 A B _93304 t R x)). Qed.
Lemma lem6997657 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : ((_93304 t R x) = (term704 A B t R x)) = ((_93304 t R x) = (term674 A B t R x)).
Proof. exact (MK_COMB (@lem6997656 A B _93304 t R x) (@lem6997655 A B t R x)). Qed.
Lemma lem6997658 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (_93304 t R x) = (term674 A B t R x).
Proof. exact (EQ_MP (@lem6997657 A B _93304 t R x) (@lem6997654 A B t R x _93304 h1)). Qed.
Lemma lem6997659 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term674 A B t R x) = (_93304 t R x).
Proof. exact (SYM (@lem6997658 A B t R x _93304 h1)). Qed.
Lemma lem6997660 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : term705 A B _93304 t R.
Proof. exact (fun x : A => @lem6997659 A B t R x _93304 h1). Qed.
Lemma lem6997661 {A B : Type'} (t : B -> Prop) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : term706 A B _93304 t.
Proof. exact (fun R : type1413 A B => @lem6997660 A B t R _93304 h1). Qed.
Lemma lem6997662 {A B : Type'} (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : term707 A B _93304.
Proof. exact (fun t : B -> Prop => @lem6997661 A B t _93304 h1). Qed.
Lemma lem6997663 {A B : Type'} (t : B -> Prop) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : term708 A B _93304 t.
Proof. exact (@lem6997662 A B _93304 h1 t). Qed.
Lemma lem6997664 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) : (term708 A B _93304 t) = (term706 A B _93304 t).
Proof. exact (eq_refl (term708 A B _93304 t)). Qed.
Lemma lem6997665 {A B : Type'} (t : B -> Prop) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : term706 A B _93304 t.
Proof. exact (EQ_MP (@lem6997664 A B _93304 t) (@lem6997663 A B t _93304 h1)). Qed.
Lemma lem6997666 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : term709 A B _93304 t R.
Proof. exact (@lem6997665 A B t _93304 h1 R). Qed.
Lemma lem6997667 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term709 A B _93304 t R) = (term705 A B _93304 t R).
Proof. exact (eq_refl (term709 A B _93304 t R)). Qed.
Lemma lem6997668 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : term705 A B _93304 t R.
Proof. exact (EQ_MP (@lem6997667 A B _93304 t R) (@lem6997666 A B t R _93304 h1)). Qed.
Lemma lem6997669 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : term710 A B _93304 t R x.
Proof. exact (@lem6997668 A B t R _93304 h1 x). Qed.
Lemma lem6997670 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term710 A B _93304 t R x) = ((term674 A B t R x) = (_93304 t R x)).
Proof. exact (eq_refl (term710 A B _93304 t R x)). Qed.
Lemma lem6997673 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term674 A B t R x) = (_93304 t R x).
Proof. exact (EQ_MP (@lem6997670 A B _93304 t R x) (@lem6997669 A B t R x _93304 h1)). Qed.
Lemma lem6997674 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term674 A B t R x) = (_93304 t R x).
Proof. exact (@lem6997673 A B t R x _93304 h1). Qed.
Lemma lem6997675 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem6997676 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term711 A B t R x) = (term712 A B _93304 t R x).
Proof. exact (MK_COMB (@lem6997675 B t) (@lem6997674 A B t R x _93304 h1)). Qed.
Lemma lem6997677 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6997678 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term713 A B t R x) = (term714 A B _93304 t R x).
Proof. exact (MK_COMB (@lem6997677) (@lem6997676 A B t R x _93304 h1)). Qed.
Lemma lem6997680 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term674 A B t R x) = (_93304 t R x).
Proof. exact (EQ_MP (@lem6997670 A B _93304 t R x) (@lem6997669 A B t R x _93304 h1)). Qed.
Lemma lem6997681 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term674 A B t R x) = (_93304 t R x).
Proof. exact (@lem6997680 A B t R x _93304 h1). Qed.
Lemma lem6997682 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (R x).
Proof. exact (eq_refl (R x)). Qed.
Lemma lem6997683 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term715 A B t R x) = (term161 A B _93304 t R x).
Proof. exact (MK_COMB (@lem6997682 A B R x) (@lem6997681 A B t R x _93304 h1)). Qed.
Lemma lem6997684 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term685 A B t R x) = (term716 A B _93304 t R x).
Proof. exact (MK_COMB (@lem6997678 A B t R x _93304 h1) (@lem6997683 A B t R x _93304 h1)). Qed.
Lemma lem6997685 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term688 A B t R x x') = (term688 A B t R x x').
Proof. exact (eq_refl (term688 A B t R x x')). Qed.
Lemma lem6997686 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (x' : A) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term690 A B x t R x') = (term717 A B x _93304 t R x').
Proof. exact (MK_COMB (@lem6997685 A B t R x' x) (@lem6997684 A B t R x' _93304 h1)). Qed.
Lemma lem6997687 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term692 A B t R x) = (term718 A B _93304 t R x).
Proof. exact (fun_ext (fun x' : B => @lem6997686 A B x' t R x _93304 h1)). Qed.
Lemma lem6997688 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6997689 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term693 A B t R x) = (term719 A B _93304 t R x).
Proof. exact (MK_COMB (@lem6997688 B) (@lem6997687 A B t R x _93304 h1)). Qed.
Lemma lem6997690 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term720 A B t R) = (term721 A B _93304 t R).
Proof. exact (fun_ext (fun x : A => @lem6997689 A B t R x _93304 h1)). Qed.
Lemma lem6997691 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6997692 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term694 A B t R) = (term722 A B _93304 t R).
Proof. exact (MK_COMB (@lem6997691 A) (@lem6997690 A B t R _93304 h1)). Qed.
Lemma lem6997693 {A B : Type'} (t : B -> Prop) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term723 A B t) = (term724 A B _93304 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem6997692 A B t R _93304 h1)). Qed.
Lemma lem6997694 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem6997695 {A B : Type'} (t : B -> Prop) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term695 A B t) = (term725 A B _93304 t).
Proof. exact (MK_COMB (@lem6997694 A B) (@lem6997693 A B t _93304 h1)). Qed.
Lemma lem6997696 {A B : Type'} (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term726 A B) = (term727 A B _93304).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6997695 A B t _93304 h1)). Qed.
Lemma lem6997697 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6997698 {A B : Type'} (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term696 A B) = (term728 A B _93304).
Proof. exact (MK_COMB (@lem6997697 B) (@lem6997696 A B _93304 h1)). Qed.
Lemma lem6997699 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6997700 {A B : Type'} (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term729 A B) = (term730 A B _93304).
Proof. exact (MK_COMB (@lem6997699) (@lem6997698 A B _93304 h1)). Qed.
Lemma lem6997702 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term674 A B t R x) = (_93304 t R x).
Proof. exact (EQ_MP (@lem6997670 A B _93304 t R x) (@lem6997669 A B t R x _93304 h1)). Qed.
Lemma lem6997703 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term674 A B t R x) = (_93304 t R x).
Proof. exact (@lem6997702 A B t R x _93304 h1). Qed.
Lemma lem6997704 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6997705 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term675 A B t R x) = (term149 A B _93304 t R x).
Proof. exact (MK_COMB (@lem6997704 B) (@lem6997703 A B t R x _93304 h1)). Qed.
Lemma lem6997706 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6997707 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : ((term674 A B t R x) = x') = ((_93304 t R x) = x').
Proof. exact (MK_COMB (@lem6997705 A B t R x _93304 h1) (@lem6997706 B x')). Qed.
Lemma lem6997708 {A : Type'} (s : A -> Prop) (x : A) : (term628 A s x) = (term628 A s x).
Proof. exact (eq_refl (term628 A s x)). Qed.
Lemma lem6997709 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term676 A B s t R x x') = (term731 A B s _93304 t R x x').
Proof. exact (MK_COMB (@lem6997708 A s x) (@lem6997707 A B t R x x' _93304 h1)). Qed.
Lemma lem6997710 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term661 A B s R x x') = (term661 A B s R x x').
Proof. exact (eq_refl (term661 A B s R x x')). Qed.
Lemma lem6997711 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : ((term660 A B s R x x') = (term676 A B s t R x x')) = ((term660 A B s R x x') = (term731 A B s _93304 t R x x')).
Proof. exact (MK_COMB (@lem6997710 A B s R x x') (@lem6997709 A B s t R x x' _93304 h1)). Qed.
Lemma lem6997712 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term678 A B s t R x) = (term732 A B s _93304 t R x).
Proof. exact (fun_ext (fun x' : A => @lem6997711 A B s t R x' x _93304 h1)). Qed.
Lemma lem6997713 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6997714 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term679 A B s t R x) = (term733 A B s _93304 t R x).
Proof. exact (MK_COMB (@lem6997713 A) (@lem6997712 A B s t R x _93304 h1)). Qed.
Lemma lem6997715 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term640 A B x t R s) = (term640 A B x t R s).
Proof. exact (eq_refl (term640 A B x t R s)). Qed.
Lemma lem6997716 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term680 A B s t R x) = (term734 A B s _93304 t R x).
Proof. exact (MK_COMB (@lem6997715 A B x t R s) (@lem6997714 A B s t R x _93304 h1)). Qed.
Lemma lem6997717 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6997718 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term682 A B s t R x) = (term735 A B s _93304 t R x).
Proof. exact (MK_COMB (@lem6997717) (@lem6997716 A B s t R x _93304 h1)). Qed.
Lemma lem6997719 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6997720 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term736 A B s t R x) = (term737 A B s _93304 t R x).
Proof. exact (MK_COMB (@lem6997719) (@lem6997718 A B s t R x _93304 h1)). Qed.
Lemma lem6997721 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem6997722 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term681 A B s t R x) = (term738 A B s _93304 t R x).
Proof. exact (MK_COMB (@lem6997720 A B s t R x _93304 h1) (@lem6997721)). Qed.
Lemma lem6997723 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term697 A B s t R x) = (term739 A B s _93304 t R x).
Proof. exact (MK_COMB (@lem6997700 A B _93304 h1) (@lem6997722 A B s t R x _93304 h1)). Qed.
Lemma lem6997724 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term740 A B s t R x) : term740 A B s t R x.
Proof. exact (h1). Qed.
Lemma lem6997725 {A B : Type'} (_93304 : type830 A B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term740 A B s t R x) : term741 A B s t R x _93304.
Proof. exact (@lem6997724 A B s t R x h1 _93304). Qed.
Lemma lem6997726 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : B) : (term741 A B s t R x _93304) = (term739 A B s _93304 t R x).
Proof. exact (eq_refl (term741 A B s t R x _93304)). Qed.
Lemma lem6997727 {A B : Type'} (_93304 : type830 A B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term740 A B s t R x) : term739 A B s _93304 t R x.
Proof. exact (EQ_MP (@lem6997726 A B s _93304 t R x) (@lem6997725 A B _93304 s t R x h1)). Qed.
Lemma lem6997728 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : (term739 A B s _93304 t R x) = (term697 A B s t R x).
Proof. exact (SYM (@lem6997723 A B s t R x _93304 h1)). Qed.
Lemma lem6997729 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (_93304 : type830 A B) (h1 : term740 A B s t R x) (h2 : _93304 = (term699 A B)) : term697 A B s t R x.
Proof. exact (EQ_MP (@lem6997728 A B s t R x _93304 h2) (@lem6997727 A B _93304 s t R x h1)). Qed.
Lemma lem6997730 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : term742 A B s t R x.
Proof. exact (fun h0 : term740 A B s t R x => @lem6997729 A B s t R x _93304 h0 h1). Qed.
Lemma lem6997731 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term743 A B s t R x.
Proof. exact (@lem51 (term697 A B s t R x) (term740 A B s t R x) (term681 A B s t R x)). Qed.
Lemma lem6997732 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : term744 A B s t R x.
Proof. exact (@lem6997731 A B s t R x (@lem6997730 A B s t R x _93304 h1)). Qed.
Lemma lem6997733 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (_93304 : type830 A B) (h1 : _93304 = (term699 A B)) : term745 A B s t R x.
Proof. exact (@lem6997732 A B s t R x _93304 h1 (@lem6997639 A B s t R x)). Qed.
Lemma lem6997734 {A B : Type'} : (term699 A B) = (term699 A B).
Proof. exact (eq_refl (term699 A B)). Qed.
Lemma lem6997735 {A B : Type'} (_93304 : type830 A B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term746 A B _93304 s t R x.
Proof. exact (fun h0 : _93304 = (term699 A B) => @lem6997733 A B s t R x _93304 h0). Qed.
Lemma lem6997736 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term747 A B s t R x.
Proof. exact (@lem6997735 A B (term699 A B) s t R x). Qed.
Lemma lem6997737 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term745 A B s t R x.
Proof. exact (@lem6997736 A B s t R x (@lem6997734 A B)). Qed.
Lemma lem6997738 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term740 A B s t R x) : term740 A B s t R x.
Proof. exact (h1). Qed.
Lemma lem6997739 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term748 A B s t R x.
Proof. exact (fun h0 : term740 A B s t R x => @lem6997738 A B s t R x h0). Qed.
Lemma lem6997740 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term749 A B s t R x.
Proof. exact (@lem51 (term740 A B s t R x) (term740 A B s t R x) (term681 A B s t R x)). Qed.
Lemma lem6997741 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term750 A B s t R x.
Proof. exact (@lem6997740 A B s t R x (@lem6997739 A B s t R x)). Qed.
Lemma lem6997742 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term745 A B s t R x.
Proof. exact (@lem6997741 A B s t R x (@lem6997737 A B s t R x)). Qed.
Lemma lem6997743 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term745 A B s t R x) : term745 A B s t R x.
Proof. exact (h1). Qed.
Lemma lem6997744 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term740 A B s t R x) : term740 A B s t R x.
Proof. exact (h1). Qed.
Lemma lem6997745 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term740 A B s t R x) (h2 : term745 A B s t R x) : term681 A B s t R x.
Proof. exact (@lem6997743 A B s t R x h2 (@lem6997744 A B s t R x h1)). Qed.
Lemma lem6997746 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term740 A B s t R x) : term751 A B s t R x.
Proof. exact (fun h0 : term745 A B s t R x => @lem6997745 A B s t R x h1 h0). Qed.
Lemma lem6997747 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term745 A B s t R x) : term745 A B s t R x.
Proof. exact (h1). Qed.
Lemma lem6997748 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term740 A B s t R x) (h2 : term745 A B s t R x) : term681 A B s t R x.
Proof. exact (@lem6997746 A B s t R x h1 (@lem6997747 A B s t R x h2)). Qed.
Lemma lem6997749 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term745 A B s t R x) : term745 A B s t R x.
Proof. exact (fun h0 : term740 A B s t R x => @lem6997748 A B s t R x h0 h1). Qed.
Lemma lem6997750 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term750 A B s t R x.
Proof. exact (fun h0 : term745 A B s t R x => @lem6997749 A B s t R x h0). Qed.
Lemma lem6997753 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term745 A B s t R x.
Proof. exact (@lem6997750 A B s t R x (@lem6997742 A B s t R x)). Qed.
Lemma lem6997754 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term745 A B s t R x.
Proof. exact (@lem6997753 A B s t R x). Qed.
Lemma lem6997800 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6997801 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : B) : (term738 A B s _93304 t R x) = (term752 A B s _93304 t R x).
Proof. exact (@lem6997800 (term735 A B s _93304 t R x)). Qed.
Lemma lem6997803 (t : Prop) : (term203 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6997804 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : B) : (term752 A B s _93304 t R x) = (term734 A B s _93304 t R x).
Proof. exact (@lem6997803 (term734 A B s _93304 t R x)). Qed.
Lemma lem6997807 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : B) : (term738 A B s _93304 t R x) = (term734 A B s _93304 t R x).
Proof. exact (TRANS (@lem6997801 A B s _93304 t R x) (@lem6997804 A B s _93304 t R x)). Qed.
Lemma lem6997828 {A B : Type'} (_93304 : type830 A B) : (term730 A B _93304) = (term730 A B _93304).
Proof. exact (eq_refl (term730 A B _93304)). Qed.
Lemma lem6997829 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : B) : (term739 A B s _93304 t R x) = (term753 A B s _93304 t R x).
Proof. exact (MK_COMB (@lem6997828 A B _93304) (@lem6997807 A B s _93304 t R x)). Qed.
Lemma lem6997832 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term754 A B s t R x) = (term755 A B s t R x).
Proof. exact (fun_ext (fun _93304 : type830 A B => @lem6997829 A B s _93304 t R x)). Qed.
Lemma lem6997833 {A B : Type'} : (@all ((B -> Prop) -> (A -> B -> Prop) -> A -> B)) = (@all ((B -> Prop) -> (A -> B -> Prop) -> A -> B)).
Proof. exact (eq_refl (@all ((B -> Prop) -> (A -> B -> Prop) -> A -> B))). Qed.
Lemma lem6997834 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term740 A B s t R x) = (term756 A B s t R x).
Proof. exact (MK_COMB (@lem6997833 A B) (@lem6997832 A B s t R x)). Qed.
Lemma lem6997839 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : B) : (term757 A B t R x) = (term758 A B t R x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6997834 A B s t R x)). Qed.
Lemma lem6997840 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6997841 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : B) : (term759 A B t R x) = (term760 A B t R x).
Proof. exact (MK_COMB (@lem6997840 A) (@lem6997839 A B t R x)). Qed.
Lemma lem6997846 {A B : Type'} (R : type1413 A B) (x : B) : (term761 A B R x) = (term762 A B R x).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6997841 A B t R x)). Qed.
Lemma lem6997847 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6997848 {A B : Type'} (R : type1413 A B) (x : B) : (term763 A B R x) = (term764 A B R x).
Proof. exact (MK_COMB (@lem6997847 B) (@lem6997846 A B R x)). Qed.
Lemma lem6997853 {A B : Type'} (x : B) : (term765 A B x) = (term766 A B x).
Proof. exact (fun_ext (fun R : type1413 A B => @lem6997848 A B R x)). Qed.
Lemma lem6997854 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem6997855 {A B : Type'} (x : B) : (term767 A B x) = (term768 A B x).
Proof. exact (MK_COMB (@lem6997854 A B) (@lem6997853 A B x)). Qed.
Lemma lem6997860 {A B : Type'} : (term769 A B) = (term770 A B).
Proof. exact (fun_ext (fun x : B => @lem6997855 A B x)). Qed.
Lemma lem6997861 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6997870 {A B : Type'} : (term771 A B) = (term772 A B).
Proof. exact (MK_COMB (@lem6997861 B) (@lem6997860 A B)). Qed.
Lemma lem6997883 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : ((term660 A B s R x x') = (term731 A B s _93304 t R x x')) = ((term660 A B s R x x') = (term731 A B s _93304 t R x x')).
Proof. exact (eq_refl ((term660 A B s R x x') = (term731 A B s _93304 t R x x'))). Qed.
Lemma lem6997884 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : B) : (term732 A B s _93304 t R x) = (term732 A B s _93304 t R x).
Proof. exact (fun_ext (fun x' : A => @lem6997883 A B s _93304 t R x' x)). Qed.
Lemma lem6997885 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6997886 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : B) : (term733 A B s _93304 t R x) = (term733 A B s _93304 t R x).
Proof. exact (MK_COMB (@lem6997885 A) (@lem6997884 A B s _93304 t R x)). Qed.
Lemma lem6997887 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem6997892 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term630 A B t R x y) = (term630 A B t R x y).
Proof. exact (eq_refl (term630 A B t R x y)). Qed.
Lemma lem6997893 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term631 A B t R x) = (term631 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem6997892 A B t R x y)). Qed.
Lemma lem6997894 {B : Type'} : (@ex1 B) = (@ex1 B).
Proof. exact (eq_refl (@ex1 B)). Qed.
Lemma lem6997895 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term632 A B t R x) = (term632 A B t R x).
Proof. exact (MK_COMB (@lem6997894 B) (@lem6997893 A B t R x)). Qed.
Lemma lem6997898 {A : Type'} (s : A -> Prop) (x : A) : (term629 A s x) = (term629 A s x).
Proof. exact (eq_refl (term629 A s x)). Qed.
Lemma lem6997899 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term633 A B s t R x) = (term633 A B s t R x).
Proof. exact (MK_COMB (@lem6997898 A s x) (@lem6997895 A B t R x)). Qed.
Lemma lem6997900 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term634 A B s t R) = (term634 A B s t R).
Proof. exact (fun_ext (fun x : A => @lem6997899 A B s t R x)). Qed.
Lemma lem6997901 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6997902 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term635 A B s t R) = (term635 A B s t R).
Proof. exact (MK_COMB (@lem6997901 A) (@lem6997900 A B s t R)). Qed.
Lemma lem6997903 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6997904 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term637 A B s t R) = (term637 A B s t R).
Proof. exact (MK_COMB (@lem6997903) (@lem6997902 A B s t R)). Qed.
Lemma lem6997905 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term638 A B t R s) = (term638 A B t R s).
Proof. exact (MK_COMB (@lem6997904 A B s t R) (@lem6997887 A s)). Qed.
Lemma lem6997908 {B : Type'} (t : B -> Prop) (x : B) : (term628 B t x) = (term628 B t x).
Proof. exact (eq_refl (term628 B t x)). Qed.
Lemma lem6997909 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term639 A B x t R s) = (term639 A B x t R s).
Proof. exact (MK_COMB (@lem6997908 B t x) (@lem6997905 A B t R s)). Qed.
Lemma lem6997910 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6997911 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term640 A B x t R s) = (term640 A B x t R s).
Proof. exact (MK_COMB (@lem6997910) (@lem6997909 A B x t R s)). Qed.
Lemma lem6997912 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : B) : (term734 A B s _93304 t R x) = (term734 A B s _93304 t R x).
Proof. exact (MK_COMB (@lem6997911 A B x t R s) (@lem6997886 A B s _93304 t R x)). Qed.
Lemma lem6997925 {A B : Type'} (x : B) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term717 A B x _93304 t R x') = (term717 A B x _93304 t R x').
Proof. exact (eq_refl (term717 A B x _93304 t R x')). Qed.
Lemma lem6997926 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term718 A B _93304 t R x) = (term718 A B _93304 t R x).
Proof. exact (fun_ext (fun x' : B => @lem6997925 A B x' _93304 t R x)). Qed.
Lemma lem6997927 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6997928 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term719 A B _93304 t R x) = (term719 A B _93304 t R x).
Proof. exact (MK_COMB (@lem6997927 B) (@lem6997926 A B _93304 t R x)). Qed.
Lemma lem6997929 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term721 A B _93304 t R) = (term721 A B _93304 t R).
Proof. exact (fun_ext (fun x : A => @lem6997928 A B _93304 t R x)). Qed.
Lemma lem6997930 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6997931 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term722 A B _93304 t R) = (term722 A B _93304 t R).
Proof. exact (MK_COMB (@lem6997930 A) (@lem6997929 A B _93304 t R)). Qed.
Lemma lem6997932 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) : (term724 A B _93304 t) = (term724 A B _93304 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem6997931 A B _93304 t R)). Qed.
Lemma lem6997933 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem6997934 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) : (term725 A B _93304 t) = (term725 A B _93304 t).
Proof. exact (MK_COMB (@lem6997933 A B) (@lem6997932 A B _93304 t)). Qed.
Lemma lem6997935 {A B : Type'} (_93304 : type830 A B) : (term727 A B _93304) = (term727 A B _93304).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6997934 A B _93304 t)). Qed.
Lemma lem6997936 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6997937 {A B : Type'} (_93304 : type830 A B) : (term728 A B _93304) = (term728 A B _93304).
Proof. exact (MK_COMB (@lem6997936 B) (@lem6997935 A B _93304)). Qed.
Lemma lem6997938 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6997939 {A B : Type'} (_93304 : type830 A B) : (term730 A B _93304) = (term730 A B _93304).
Proof. exact (MK_COMB (@lem6997938) (@lem6997937 A B _93304)). Qed.
Lemma lem6997940 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : B) : (term753 A B s _93304 t R x) = (term753 A B s _93304 t R x).
Proof. exact (MK_COMB (@lem6997939 A B _93304) (@lem6997912 A B s _93304 t R x)). Qed.
Lemma lem6997941 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term755 A B s t R x) = (term755 A B s t R x).
Proof. exact (fun_ext (fun _93304 : type830 A B => @lem6997940 A B s _93304 t R x)). Qed.
Lemma lem6997942 {A B : Type'} : (@all ((B -> Prop) -> (A -> B -> Prop) -> A -> B)) = (@all ((B -> Prop) -> (A -> B -> Prop) -> A -> B)).
Proof. exact (eq_refl (@all ((B -> Prop) -> (A -> B -> Prop) -> A -> B))). Qed.
Lemma lem6997943 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term756 A B s t R x) = (term756 A B s t R x).
Proof. exact (MK_COMB (@lem6997942 A B) (@lem6997941 A B s t R x)). Qed.
Lemma lem6997944 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : B) : (term758 A B t R x) = (term758 A B t R x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6997943 A B s t R x)). Qed.
Lemma lem6997945 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6997946 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : B) : (term760 A B t R x) = (term760 A B t R x).
Proof. exact (MK_COMB (@lem6997945 A) (@lem6997944 A B t R x)). Qed.
Lemma lem6997947 {A B : Type'} (R : type1413 A B) (x : B) : (term762 A B R x) = (term762 A B R x).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6997946 A B t R x)). Qed.
Lemma lem6997948 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6997949 {A B : Type'} (R : type1413 A B) (x : B) : (term764 A B R x) = (term764 A B R x).
Proof. exact (MK_COMB (@lem6997948 B) (@lem6997947 A B R x)). Qed.
Lemma lem6997950 {A B : Type'} (x : B) : (term766 A B x) = (term766 A B x).
Proof. exact (fun_ext (fun R : type1413 A B => @lem6997949 A B R x)). Qed.
Lemma lem6997951 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem6997952 {A B : Type'} (x : B) : (term768 A B x) = (term768 A B x).
Proof. exact (MK_COMB (@lem6997951 A B) (@lem6997950 A B x)). Qed.
Lemma lem6997953 {A B : Type'} : (term770 A B) = (term770 A B).
Proof. exact (fun_ext (fun x : B => @lem6997952 A B x)). Qed.
Lemma lem6997954 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6997955 {A B : Type'} : (term772 A B) = (term772 A B).
Proof. exact (MK_COMB (@lem6997954 B) (@lem6997953 A B)). Qed.
Lemma lem6998046 {A B : Type'} : (term771 A B) = (term772 A B).
Proof. exact (TRANS (@lem6997870 A B) (@lem6997955 A B)). Qed.
Lemma lem6998047 {A B : Type'} : (term772 A B) = (term771 A B).
Proof. exact (SYM (@lem6998046 A B)). Qed.
Lemma lem6998048 {A B : Type'} (_93304 : type830 A B) (h1 : term728 A B _93304) : term728 A B _93304.
Proof. exact (h1). Qed.
Lemma lem6998049 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term639 A B x t R s) : term639 A B x t R s.
Proof. exact (h1). Qed.
Lemma lem6998051 (p : Prop) : p = (term120 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6998052 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : ((term660 A B s R x' x) = (term731 A B s _93304 t R x' x)) = (term773 A B s _93304 t R x' x).
Proof. exact (@lem6998051 ((term660 A B s R x' x) = (term731 A B s _93304 t R x' x))). Qed.
Lemma lem6998053 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term773 A B s _93304 t R x' x) = ((term660 A B s R x' x) = (term731 A B s _93304 t R x' x)).
Proof. exact (SYM (@lem6998052 A B s _93304 t R x' x)). Qed.
Lemma lem6998054 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term774 A B s _93304 t R x' x) : term774 A B s _93304 t R x' x.
Proof. exact (h1). Qed.
Lemma lem6998061 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term775 A B t R x x') = (term776 A B t R x x').
Proof. exact (@lem17045 (t x') (R x x')). Qed.
Lemma lem6998066 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term716 A B _93304 t R x) = (term716 A B _93304 t R x).
Proof. exact (eq_refl (term716 A B _93304 t R x)). Qed.
Lemma lem6998067 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6998068 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term777 A B t R x x') = (term778 A B t R x x').
Proof. exact (MK_COMB (@lem6998067) (@lem6998061 A B t R x x')). Qed.
Lemma lem6998069 {A B : Type'} (x : B) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term779 A B x _93304 t R x') = (term780 A B x _93304 t R x').
Proof. exact (MK_COMB (@lem6998068 A B t R x' x) (@lem6998066 A B _93304 t R x')). Qed.
Lemma lem6998070 {A B : Type'} (x : B) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term717 A B x _93304 t R x') = (term779 A B x _93304 t R x').
Proof. exact (@lem17265 (term630 A B t R x' x) (term716 A B _93304 t R x')). Qed.
Lemma lem6998071 {A B : Type'} (x : B) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term717 A B x _93304 t R x') = (term780 A B x _93304 t R x').
Proof. exact (TRANS (@lem6998070 A B x _93304 t R x') (@lem6998069 A B x _93304 t R x')). Qed.
Lemma lem6998072 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term718 A B _93304 t R x) = (term781 A B _93304 t R x).
Proof. exact (fun_ext (fun x' : B => @lem6998071 A B x' _93304 t R x)). Qed.
Lemma lem6998073 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6998074 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term719 A B _93304 t R x) = (term782 A B _93304 t R x).
Proof. exact (MK_COMB (@lem6998073 B) (@lem6998072 A B _93304 t R x)). Qed.
Lemma lem6998075 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term721 A B _93304 t R) = (term783 A B _93304 t R).
Proof. exact (fun_ext (fun x : A => @lem6998074 A B _93304 t R x)). Qed.
Lemma lem6998076 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6998077 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term722 A B _93304 t R) = (term784 A B _93304 t R).
Proof. exact (MK_COMB (@lem6998076 A) (@lem6998075 A B _93304 t R)). Qed.
Lemma lem6998078 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) : (term724 A B _93304 t) = (term785 A B _93304 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem6998077 A B _93304 t R)). Qed.
Lemma lem6998079 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem6998080 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) : (term725 A B _93304 t) = (term786 A B _93304 t).
Proof. exact (MK_COMB (@lem6998079 A B) (@lem6998078 A B _93304 t)). Qed.
Lemma lem6998081 {A B : Type'} (_93304 : type830 A B) : (term727 A B _93304) = (term787 A B _93304).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6998080 A B _93304 t)). Qed.
Lemma lem6998082 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6998083 {A B : Type'} (_93304 : type830 A B) : (term728 A B _93304) = (term788 A B _93304).
Proof. exact (MK_COMB (@lem6998082 B) (@lem6998081 A B _93304)). Qed.
Lemma lem6998117 {A : Type'} (P : A -> Prop) (Q : Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem6998118 {B : Type'} (P : B -> Prop) (Q : Prop) : (term241 B P Q) = (term242 B P Q).
Proof. exact (@lem6998117 B P Q). Qed.
Lemma lem6998119 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term789 A B _93304 t R x) = (term790 A B _93304 t R x).
Proof. exact (@lem6998118 B (term791 A B t R x) (term716 A B _93304 t R x)). Qed.
Lemma lem6998120 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term792 A B t R x x') = (term776 A B t R x x').
Proof. exact (eq_refl (term792 A B t R x x')). Qed.
Lemma lem6998121 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6998122 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term793 A B t R x x') = (term778 A B t R x x').
Proof. exact (MK_COMB (@lem6998121) (@lem6998120 A B t R x x')). Qed.
Lemma lem6998123 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term716 A B _93304 t R x) = (term716 A B _93304 t R x).
Proof. exact (eq_refl (term716 A B _93304 t R x)). Qed.
Lemma lem6998124 {A B : Type'} (x : B) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term794 A B x _93304 t R x') = (term780 A B x _93304 t R x').
Proof. exact (MK_COMB (@lem6998122 A B t R x' x) (@lem6998123 A B _93304 t R x')). Qed.
Lemma lem6998125 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term795 A B _93304 t R x) = (term781 A B _93304 t R x).
Proof. exact (fun_ext (fun x' : B => @lem6998124 A B x' _93304 t R x)). Qed.
Lemma lem6998126 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6998127 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term789 A B _93304 t R x) = (term782 A B _93304 t R x).
Proof. exact (MK_COMB (@lem6998126 B) (@lem6998125 A B _93304 t R x)). Qed.
Lemma lem6998128 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6998129 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term796 A B _93304 t R x) = (term797 A B _93304 t R x).
Proof. exact (MK_COMB (@lem6998128) (@lem6998127 A B _93304 t R x)). Qed.
Lemma lem6998130 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term792 A B t R x x') = (term776 A B t R x x').
Proof. exact (eq_refl (term792 A B t R x x')). Qed.
Lemma lem6998131 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term798 A B t R x) = (term791 A B t R x).
Proof. exact (fun_ext (fun x' : B => @lem6998130 A B t R x x')). Qed.
Lemma lem6998132 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6998133 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term799 A B t R x) = (term800 A B t R x).
Proof. exact (MK_COMB (@lem6998132 B) (@lem6998131 A B t R x)). Qed.
Lemma lem6998134 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6998135 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term801 A B t R x) = (term802 A B t R x).
Proof. exact (MK_COMB (@lem6998134) (@lem6998133 A B t R x)). Qed.
Lemma lem6998136 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term716 A B _93304 t R x) = (term716 A B _93304 t R x).
Proof. exact (eq_refl (term716 A B _93304 t R x)). Qed.
Lemma lem6998137 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term790 A B _93304 t R x) = (term803 A B _93304 t R x).
Proof. exact (MK_COMB (@lem6998135 A B t R x) (@lem6998136 A B _93304 t R x)). Qed.
Lemma lem6998138 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : ((term789 A B _93304 t R x) = (term790 A B _93304 t R x)) = ((term782 A B _93304 t R x) = (term803 A B _93304 t R x)).
Proof. exact (MK_COMB (@lem6998129 A B _93304 t R x) (@lem6998137 A B _93304 t R x)). Qed.
Lemma lem6998139 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term782 A B _93304 t R x) = (term803 A B _93304 t R x).
Proof. exact (EQ_MP (@lem6998138 A B _93304 t R x) (@lem6998119 A B _93304 t R x)). Qed.
Lemma lem6998188 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term783 A B _93304 t R) = (term804 A B _93304 t R).
Proof. exact (fun_ext (fun x : A => @lem6998139 A B _93304 t R x)). Qed.
Lemma lem6998189 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6998190 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term784 A B _93304 t R) = (term805 A B _93304 t R).
Proof. exact (MK_COMB (@lem6998189 A) (@lem6998188 A B _93304 t R)). Qed.
Lemma lem6998239 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) : (term785 A B _93304 t) = (term806 A B _93304 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem6998190 A B _93304 t R)). Qed.
Lemma lem6998240 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem6998241 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) : (term786 A B _93304 t) = (term807 A B _93304 t).
Proof. exact (MK_COMB (@lem6998240 A B) (@lem6998239 A B _93304 t)). Qed.
Lemma lem6998246 {A B : Type'} (_93304 : type830 A B) : (term787 A B _93304) = (term808 A B _93304).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6998241 A B _93304 t)). Qed.
Lemma lem6998247 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6998254 {A B : Type'} (_93304 : type830 A B) : (term788 A B _93304) = (term809 A B _93304).
Proof. exact (MK_COMB (@lem6998247 B) (@lem6998246 A B _93304)). Qed.
Lemma lem6998255 {A B : Type'} (_93304 : type830 A B) : (term728 A B _93304) = (term809 A B _93304).
Proof. exact (TRANS (@lem6998083 A B _93304) (@lem6998254 A B _93304)). Qed.
Lemma lem6998256 {A B : Type'} (_93304 : type830 A B) (h1 : term728 A B _93304) : term809 A B _93304.
Proof. exact (EQ_MP (@lem6998255 A B _93304) (@lem6998048 A B _93304 h1)). Qed.
Lemma lem6998267 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term775 A B t R x y) = (term776 A B t R x y).
Proof. exact (@lem17045 (t y) (R x y)). Qed.
Lemma lem6998272 {B : Type'} (y' : B) (y : B) : (y' = y) = (y' = y).
Proof. exact (eq_refl (y' = y)). Qed.
Lemma lem6998273 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term686 A B t R x y) = (term630 A B t R x y).
Proof. exact (eq_refl (term686 A B t R x y)). Qed.
Lemma lem6998274 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term686 A B t R x y') = (term630 A B t R x y').
Proof. exact (eq_refl (term686 A B t R x y')). Qed.
Lemma lem6998275 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term775 A B t R x y') = (term776 A B t R x y').
Proof. exact (@lem6998267 A B t R x y'). Qed.
Lemma lem6998276 {B : Type'} (P : B -> Prop) : (@ex1 B P) = (term264 B P).
Proof. exact (@lem18897 B P). Qed.
Lemma lem6998277 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term632 A B t R x) = (term810 A B t R x).
Proof. exact (@lem6998276 B (term631 A B t R x)). Qed.
Lemma lem6998278 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6998279 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term811 A B t R x y') = (term775 A B t R x y').
Proof. exact (MK_COMB (@lem6998278) (@lem6998274 A B t R x y')). Qed.
Lemma lem6998280 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term811 A B t R x y') = (term776 A B t R x y').
Proof. exact (TRANS (@lem6998279 A B t R x y') (@lem6998275 A B t R x y')). Qed.
Lemma lem6998281 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6998282 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term812 A B t R x y') = (term778 A B t R x y').
Proof. exact (MK_COMB (@lem6998281) (@lem6998280 A B t R x y')). Qed.
Lemma lem6998283 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term813 A B t R x y' y) = (term814 A B t R x y' y).
Proof. exact (MK_COMB (@lem6998282 A B t R x y') (@lem6998272 B y' y)). Qed.
Lemma lem6998284 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6998285 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term811 A B t R x y) = (term775 A B t R x y).
Proof. exact (MK_COMB (@lem6998284) (@lem6998273 A B t R x y)). Qed.
Lemma lem6998286 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term811 A B t R x y) = (term776 A B t R x y).
Proof. exact (TRANS (@lem6998285 A B t R x y) (@lem6998267 A B t R x y)). Qed.
Lemma lem6998287 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6998288 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term812 A B t R x y) = (term778 A B t R x y).
Proof. exact (MK_COMB (@lem6998287) (@lem6998286 A B t R x y)). Qed.
Lemma lem6998289 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term815 A B t R x y' y) = (term816 A B t R x y' y).
Proof. exact (MK_COMB (@lem6998288 A B t R x y) (@lem6998283 A B t R x y' y)). Qed.
Lemma lem6998290 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term817 A B t R x y) = (term818 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem6998289 A B t R x y' y)). Qed.
Lemma lem6998291 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6998292 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term819 A B t R x y) = (term820 A B t R x y).
Proof. exact (MK_COMB (@lem6998291 B) (@lem6998290 A B t R x y)). Qed.
Lemma lem6998293 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term821 A B t R x) = (term822 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem6998292 A B t R x y)). Qed.
Lemma lem6998294 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6998295 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term823 A B t R x) = (term824 A B t R x).
Proof. exact (MK_COMB (@lem6998294 B) (@lem6998293 A B t R x)). Qed.
Lemma lem6998296 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term686 A B t R x y) = (term630 A B t R x y).
Proof. exact (eq_refl (term686 A B t R x y)). Qed.
Lemma lem6998297 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term825 A B t R x) = (term631 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem6998296 A B t R x y)). Qed.
Lemma lem6998298 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6998299 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term826 A B t R x) = (term827 A B t R x).
Proof. exact (MK_COMB (@lem6998298 B) (@lem6998297 A B t R x)). Qed.
Lemma lem6998300 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6998301 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term828 A B t R x) = (term829 A B t R x).
Proof. exact (MK_COMB (@lem6998300) (@lem6998299 A B t R x)). Qed.
Lemma lem6998302 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term810 A B t R x) = (term830 A B t R x).
Proof. exact (MK_COMB (@lem6998301 A B t R x) (@lem6998295 A B t R x)). Qed.
Lemma lem6998303 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term632 A B t R x) = (term830 A B t R x).
Proof. exact (TRANS (@lem6998277 A B t R x) (@lem6998302 A B t R x)). Qed.
Lemma lem6998305 {A : Type'} (s : A -> Prop) (x : A) : (term831 A s x) = (term831 A s x).
Proof. exact (eq_refl (term831 A s x)). Qed.
Lemma lem6998306 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term832 A B s t R x) = (term833 A B s t R x).
Proof. exact (MK_COMB (@lem6998305 A s x) (@lem6998303 A B t R x)). Qed.
Lemma lem6998307 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term633 A B s t R x) = (term832 A B s t R x).
Proof. exact (@lem17265 (s x) (term632 A B t R x)). Qed.
Lemma lem6998308 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term633 A B s t R x) = (term833 A B s t R x).
Proof. exact (TRANS (@lem6998307 A B s t R x) (@lem6998306 A B s t R x)). Qed.
Lemma lem6998309 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term634 A B s t R) = (term834 A B s t R).
Proof. exact (fun_ext (fun x : A => @lem6998308 A B s t R x)). Qed.
Lemma lem6998310 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6998311 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term635 A B s t R) = (term835 A B s t R).
Proof. exact (MK_COMB (@lem6998310 A) (@lem6998309 A B s t R)). Qed.
Lemma lem6998312 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem6998313 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6998314 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term637 A B s t R) = (term836 A B s t R).
Proof. exact (MK_COMB (@lem6998313) (@lem6998311 A B s t R)). Qed.
Lemma lem6998315 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term638 A B t R s) = (term837 A B t R s).
Proof. exact (MK_COMB (@lem6998314 A B s t R) (@lem6998312 A s)). Qed.
Lemma lem6998317 {B : Type'} (t : B -> Prop) (x : B) : (term628 B t x) = (term628 B t x).
Proof. exact (eq_refl (term628 B t x)). Qed.
Lemma lem6998318 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term639 A B x t R s) = (term838 A B x t R s).
Proof. exact (MK_COMB (@lem6998317 B t x) (@lem6998315 A B t R s)). Qed.
Lemma lem6998400 {A : Type'} (P : Prop) (Q : A -> Prop) : (term291 A P Q) = (term292 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem6998401 {B : Type'} (P : Prop) (Q : B -> Prop) : (term291 B P Q) = (term292 B P Q).
Proof. exact (@lem6998400 B P Q). Qed.
Lemma lem6998402 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term839 A B t R x y) = (term840 A B t R x y).
Proof. exact (@lem6998401 B (term776 A B t R x y) (term841 A B t R x y)). Qed.
Lemma lem6998403 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term842 A B t R x y y') = (term814 A B t R x y' y).
Proof. exact (eq_refl (term842 A B t R x y y')). Qed.
Lemma lem6998404 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term778 A B t R x y) = (term778 A B t R x y).
Proof. exact (eq_refl (term778 A B t R x y)). Qed.
Lemma lem6998405 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term843 A B t R x y y') = (term816 A B t R x y' y).
Proof. exact (MK_COMB (@lem6998404 A B t R x y) (@lem6998403 A B t R x y' y)). Qed.
Lemma lem6998406 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term844 A B t R x y) = (term818 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem6998405 A B t R x y' y)). Qed.
Lemma lem6998407 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6998408 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term839 A B t R x y) = (term820 A B t R x y).
Proof. exact (MK_COMB (@lem6998407 B) (@lem6998406 A B t R x y)). Qed.
Lemma lem6998409 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6998410 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term845 A B t R x y) = (term846 A B t R x y).
Proof. exact (MK_COMB (@lem6998409) (@lem6998408 A B t R x y)). Qed.
Lemma lem6998411 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term842 A B t R x y y') = (term814 A B t R x y' y).
Proof. exact (eq_refl (term842 A B t R x y y')). Qed.
Lemma lem6998412 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term847 A B t R x y) = (term841 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem6998411 A B t R x y' y)). Qed.
Lemma lem6998413 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6998414 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term848 A B t R x y) = (term849 A B t R x y).
Proof. exact (MK_COMB (@lem6998413 B) (@lem6998412 A B t R x y)). Qed.
Lemma lem6998415 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term778 A B t R x y) = (term778 A B t R x y).
Proof. exact (eq_refl (term778 A B t R x y)). Qed.
Lemma lem6998416 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term840 A B t R x y) = (term850 A B t R x y).
Proof. exact (MK_COMB (@lem6998415 A B t R x y) (@lem6998414 A B t R x y)). Qed.
Lemma lem6998417 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : ((term839 A B t R x y) = (term840 A B t R x y)) = ((term820 A B t R x y) = (term850 A B t R x y)).
Proof. exact (MK_COMB (@lem6998410 A B t R x y) (@lem6998416 A B t R x y)). Qed.
Lemma lem6998418 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term820 A B t R x y) = (term850 A B t R x y).
Proof. exact (EQ_MP (@lem6998417 A B t R x y) (@lem6998402 A B t R x y)). Qed.
Lemma lem6998467 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term822 A B t R x) = (term851 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem6998418 A B t R x y)). Qed.
Lemma lem6998468 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6998469 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term824 A B t R x) = (term852 A B t R x).
Proof. exact (MK_COMB (@lem6998468 B) (@lem6998467 A B t R x)). Qed.
Lemma lem6998518 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term829 A B t R x) = (term829 A B t R x).
Proof. exact (eq_refl (term829 A B t R x)). Qed.
Lemma lem6998519 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term830 A B t R x) = (term853 A B t R x).
Proof. exact (MK_COMB (@lem6998518 A B t R x) (@lem6998469 A B t R x)). Qed.
Lemma lem6998520 {A : Type'} (s : A -> Prop) (x : A) : (term831 A s x) = (term831 A s x).
Proof. exact (eq_refl (term831 A s x)). Qed.
Lemma lem6998521 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term833 A B s t R x) = (term854 A B s t R x).
Proof. exact (MK_COMB (@lem6998520 A s x) (@lem6998519 A B t R x)). Qed.
Lemma lem6998522 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term834 A B s t R) = (term855 A B s t R).
Proof. exact (fun_ext (fun x : A => @lem6998521 A B s t R x)). Qed.
Lemma lem6998523 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6998524 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term835 A B s t R) = (term856 A B s t R).
Proof. exact (MK_COMB (@lem6998523 A) (@lem6998522 A B s t R)). Qed.
Lemma lem6998573 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6998574 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term836 A B s t R) = (term857 A B s t R).
Proof. exact (MK_COMB (@lem6998573) (@lem6998524 A B s t R)). Qed.
Lemma lem6998575 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem6998576 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term837 A B t R s) = (term858 A B t R s).
Proof. exact (MK_COMB (@lem6998574 A B s t R) (@lem6998575 A s)). Qed.
Lemma lem6998577 {B : Type'} (t : B -> Prop) (x : B) : (term628 B t x) = (term628 B t x).
Proof. exact (eq_refl (term628 B t x)). Qed.
Lemma lem6998578 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term838 A B x t R s) = (term859 A B x t R s).
Proof. exact (MK_COMB (@lem6998577 B t x) (@lem6998576 A B t R s)). Qed.
Lemma lem6998580 {A : Type'} (P : A -> Prop) (Q : Prop) : (term311 A P Q) = (term312 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6998581 {B : Type'} (P : B -> Prop) (Q : Prop) : (term311 B P Q) = (term312 B P Q).
Proof. exact (@lem6998580 B P Q). Qed.
Lemma lem6998582 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term860 A B t R x) = (term861 A B t R x).
Proof. exact (@lem6998581 B (term631 A B t R x) (term852 A B t R x)). Qed.
Lemma lem6998583 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term686 A B t R x y) = (term630 A B t R x y).
Proof. exact (eq_refl (term686 A B t R x y)). Qed.
Lemma lem6998584 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term825 A B t R x) = (term631 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem6998583 A B t R x y)). Qed.
Lemma lem6998585 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6998586 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term826 A B t R x) = (term827 A B t R x).
Proof. exact (MK_COMB (@lem6998585 B) (@lem6998584 A B t R x)). Qed.
Lemma lem6998587 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6998588 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term828 A B t R x) = (term829 A B t R x).
Proof. exact (MK_COMB (@lem6998587) (@lem6998586 A B t R x)). Qed.
Lemma lem6998589 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term852 A B t R x) = (term852 A B t R x).
Proof. exact (eq_refl (term852 A B t R x)). Qed.
Lemma lem6998590 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term860 A B t R x) = (term853 A B t R x).
Proof. exact (MK_COMB (@lem6998588 A B t R x) (@lem6998589 A B t R x)). Qed.
Lemma lem6998591 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6998592 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term862 A B t R x) = (term863 A B t R x).
Proof. exact (MK_COMB (@lem6998591) (@lem6998590 A B t R x)). Qed.
Lemma lem6998593 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term686 A B t R x y) = (term630 A B t R x y).
Proof. exact (eq_refl (term686 A B t R x y)). Qed.
Lemma lem6998594 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6998595 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term864 A B t R x y) = (term865 A B t R x y).
Proof. exact (MK_COMB (@lem6998594) (@lem6998593 A B t R x y)). Qed.
Lemma lem6998596 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term852 A B t R x) = (term852 A B t R x).
Proof. exact (eq_refl (term852 A B t R x)). Qed.
Lemma lem6998597 {A B : Type'} (y : B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term866 A B y t R x) = (term867 A B y t R x).
Proof. exact (MK_COMB (@lem6998595 A B t R x y) (@lem6998596 A B t R x)). Qed.
Lemma lem6998598 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term868 A B t R x) = (term869 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem6998597 A B y t R x)). Qed.
Lemma lem6998599 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6998600 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term861 A B t R x) = (term870 A B t R x).
Proof. exact (MK_COMB (@lem6998599 B) (@lem6998598 A B t R x)). Qed.
Lemma lem6998601 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : ((term860 A B t R x) = (term861 A B t R x)) = ((term853 A B t R x) = (term870 A B t R x)).
Proof. exact (MK_COMB (@lem6998592 A B t R x) (@lem6998600 A B t R x)). Qed.
Lemma lem6998602 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term853 A B t R x) = (term870 A B t R x).
Proof. exact (EQ_MP (@lem6998601 A B t R x) (@lem6998582 A B t R x)). Qed.
Lemma lem6998603 {A : Type'} (s : A -> Prop) (x : A) : (term831 A s x) = (term831 A s x).
Proof. exact (eq_refl (term831 A s x)). Qed.
Lemma lem6998604 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term854 A B s t R x) = (term871 A B s t R x).
Proof. exact (MK_COMB (@lem6998603 A s x) (@lem6998602 A B t R x)). Qed.
Lemma lem6998606 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6998607 {B : Type'} (P : Prop) (Q : B -> Prop) : (term325 B P Q) = (term326 B P Q).
Proof. exact (@lem6998606 B P Q). Qed.
Lemma lem6998608 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term872 A B s t R x) = (term873 A B s t R x).
Proof. exact (@lem6998607 B (term874 A s x) (term869 A B t R x)). Qed.
Lemma lem6998609 {A B : Type'} (y : B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term875 A B t R x y) = (term867 A B y t R x).
Proof. exact (eq_refl (term875 A B t R x y)). Qed.
Lemma lem6998610 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term876 A B t R x) = (term869 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem6998609 A B y t R x)). Qed.
Lemma lem6998611 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6998612 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term877 A B t R x) = (term870 A B t R x).
Proof. exact (MK_COMB (@lem6998611 B) (@lem6998610 A B t R x)). Qed.
Lemma lem6998613 {A : Type'} (s : A -> Prop) (x : A) : (term831 A s x) = (term831 A s x).
Proof. exact (eq_refl (term831 A s x)). Qed.
Lemma lem6998614 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term872 A B s t R x) = (term871 A B s t R x).
Proof. exact (MK_COMB (@lem6998613 A s x) (@lem6998612 A B t R x)). Qed.
Lemma lem6998615 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6998616 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term878 A B s t R x) = (term879 A B s t R x).
Proof. exact (MK_COMB (@lem6998615) (@lem6998614 A B s t R x)). Qed.
Lemma lem6998617 {A B : Type'} (y : B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term875 A B t R x y) = (term867 A B y t R x).
Proof. exact (eq_refl (term875 A B t R x y)). Qed.
Lemma lem6998618 {A : Type'} (s : A -> Prop) (x : A) : (term831 A s x) = (term831 A s x).
Proof. exact (eq_refl (term831 A s x)). Qed.
Lemma lem6998619 {A B : Type'} (s : A -> Prop) (y : B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term880 A B s t R x y) = (term881 A B s y t R x).
Proof. exact (MK_COMB (@lem6998618 A s x) (@lem6998617 A B y t R x)). Qed.
Lemma lem6998620 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term882 A B s t R x) = (term883 A B s t R x).
Proof. exact (fun_ext (fun y : B => @lem6998619 A B s y t R x)). Qed.
Lemma lem6998621 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6998622 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term873 A B s t R x) = (term884 A B s t R x).
Proof. exact (MK_COMB (@lem6998621 B) (@lem6998620 A B s t R x)). Qed.
Lemma lem6998623 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : ((term872 A B s t R x) = (term873 A B s t R x)) = ((term871 A B s t R x) = (term884 A B s t R x)).
Proof. exact (MK_COMB (@lem6998616 A B s t R x) (@lem6998622 A B s t R x)). Qed.
Lemma lem6998624 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term871 A B s t R x) = (term884 A B s t R x).
Proof. exact (EQ_MP (@lem6998623 A B s t R x) (@lem6998608 A B s t R x)). Qed.
Lemma lem6998625 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term854 A B s t R x) = (term884 A B s t R x).
Proof. exact (TRANS (@lem6998604 A B s t R x) (@lem6998624 A B s t R x)). Qed.
Lemma lem6998626 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term855 A B s t R) = (term885 A B s t R).
Proof. exact (fun_ext (fun x : A => @lem6998625 A B s t R x)). Qed.
Lemma lem6998627 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6998628 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term856 A B s t R) = (term886 A B s t R).
Proof. exact (MK_COMB (@lem6998627 A) (@lem6998626 A B s t R)). Qed.
Lemma lem6998630 {A B : Type'} (P : type1413 A B) : (term342 A B P) = (term343 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6998631 {A B : Type'} (P : type1413 A B) : (term342 A B P) = (term343 A B P).
Proof. exact (@lem6998630 A B P). Qed.
Lemma lem6998632 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term887 A B s t R) = (term888 A B s t R).
Proof. exact (@lem6998631 A B (term889 A B s t R)). Qed.
Lemma lem6998633 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term890 A B s t R x) = (term883 A B s t R x).
Proof. exact (eq_refl (term890 A B s t R x)). Qed.
Lemma lem6998634 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6998635 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term891 A B s t R x y) = (term892 A B s t R x y).
Proof. exact (MK_COMB (@lem6998633 A B s t R x) (@lem6998634 B y)). Qed.
Lemma lem6998636 {A B : Type'} (s : A -> Prop) (y : B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term892 A B s t R x y) = (term881 A B s y t R x).
Proof. exact (eq_refl (term892 A B s t R x y)). Qed.
Lemma lem6998637 {A B : Type'} (s : A -> Prop) (y : B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term891 A B s t R x y) = (term881 A B s y t R x).
Proof. exact (TRANS (@lem6998635 A B s t R x y) (@lem6998636 A B s y t R x)). Qed.
Lemma lem6998638 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term893 A B s t R x) = (term883 A B s t R x).
Proof. exact (fun_ext (fun y : B => @lem6998637 A B s y t R x)). Qed.
Lemma lem6998639 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6998640 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term894 A B s t R x) = (term884 A B s t R x).
Proof. exact (MK_COMB (@lem6998639 B) (@lem6998638 A B s t R x)). Qed.
Lemma lem6998641 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term895 A B s t R) = (term885 A B s t R).
Proof. exact (fun_ext (fun x : A => @lem6998640 A B s t R x)). Qed.
Lemma lem6998642 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6998643 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term887 A B s t R) = (term886 A B s t R).
Proof. exact (MK_COMB (@lem6998642 A) (@lem6998641 A B s t R)). Qed.
Lemma lem6998644 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6998645 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term896 A B s t R) = (term897 A B s t R).
Proof. exact (MK_COMB (@lem6998644) (@lem6998643 A B s t R)). Qed.
Lemma lem6998646 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term890 A B s t R x) = (term883 A B s t R x).
Proof. exact (eq_refl (term890 A B s t R x)). Qed.
Lemma lem6998647 {A B : Type'} (y : A -> B) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem6998648 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term898 A B s t R y x) = (term899 A B s t R y x).
Proof. exact (MK_COMB (@lem6998646 A B s t R x) (@lem6998647 A B y x)). Qed.
Lemma lem6998649 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term899 A B s t R y x) = (term900 A B s y t R x).
Proof. exact (eq_refl (term899 A B s t R y x)). Qed.
Lemma lem6998650 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term898 A B s t R y x) = (term900 A B s y t R x).
Proof. exact (TRANS (@lem6998648 A B s t R y x) (@lem6998649 A B s y t R x)). Qed.
Lemma lem6998651 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term901 A B s t R y) = (term902 A B s y t R).
Proof. exact (fun_ext (fun x : A => @lem6998650 A B s y t R x)). Qed.
Lemma lem6998652 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6998653 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term903 A B s t R y) = (term904 A B s y t R).
Proof. exact (MK_COMB (@lem6998652 A) (@lem6998651 A B s y t R)). Qed.
Lemma lem6998654 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term905 A B s t R) = (term906 A B s t R).
Proof. exact (fun_ext (fun y : A -> B => @lem6998653 A B s y t R)). Qed.
Lemma lem6998655 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem6998656 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term888 A B s t R) = (term907 A B s t R).
Proof. exact (MK_COMB (@lem6998655 A B) (@lem6998654 A B s t R)). Qed.
Lemma lem6998657 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : ((term887 A B s t R) = (term888 A B s t R)) = ((term886 A B s t R) = (term907 A B s t R)).
Proof. exact (MK_COMB (@lem6998645 A B s t R) (@lem6998656 A B s t R)). Qed.
Lemma lem6998658 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term886 A B s t R) = (term907 A B s t R).
Proof. exact (EQ_MP (@lem6998657 A B s t R) (@lem6998632 A B s t R)). Qed.
Lemma lem6998659 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term856 A B s t R) = (term907 A B s t R).
Proof. exact (TRANS (@lem6998628 A B s t R) (@lem6998658 A B s t R)). Qed.
Lemma lem6998660 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6998661 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term857 A B s t R) = (term908 A B s t R).
Proof. exact (MK_COMB (@lem6998660) (@lem6998659 A B s t R)). Qed.
Lemma lem6998662 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem6998663 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term858 A B t R s) = (term909 A B t R s).
Proof. exact (MK_COMB (@lem6998661 A B s t R) (@lem6998662 A s)). Qed.
Lemma lem6998665 {A : Type'} (P : A -> Prop) (Q : Prop) : (term311 A P Q) = (term312 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6998666 {A B : Type'} (P : type572 A B) (Q : Prop) : (term910 A B P Q) = (term911 A B P Q).
Proof. exact (@lem6998665 (A -> B) P Q). Qed.
Lemma lem6998667 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term912 A B t R s) = (term913 A B t R s).
Proof. exact (@lem6998666 A B (term906 A B s t R) (@FINITE A s)). Qed.
Lemma lem6998668 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term914 A B s t R y) = (term904 A B s y t R).
Proof. exact (eq_refl (term914 A B s t R y)). Qed.
Lemma lem6998669 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term915 A B s t R) = (term906 A B s t R).
Proof. exact (fun_ext (fun y : A -> B => @lem6998668 A B s y t R)). Qed.
Lemma lem6998670 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem6998671 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term916 A B s t R) = (term907 A B s t R).
Proof. exact (MK_COMB (@lem6998670 A B) (@lem6998669 A B s t R)). Qed.
Lemma lem6998672 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6998673 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term917 A B s t R) = (term908 A B s t R).
Proof. exact (MK_COMB (@lem6998672) (@lem6998671 A B s t R)). Qed.
Lemma lem6998674 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem6998675 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term912 A B t R s) = (term909 A B t R s).
Proof. exact (MK_COMB (@lem6998673 A B s t R) (@lem6998674 A s)). Qed.
Lemma lem6998676 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6998677 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term918 A B t R s) = (term919 A B t R s).
Proof. exact (MK_COMB (@lem6998676) (@lem6998675 A B t R s)). Qed.
Lemma lem6998678 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term914 A B s t R y) = (term904 A B s y t R).
Proof. exact (eq_refl (term914 A B s t R y)). Qed.
Lemma lem6998679 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6998680 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term920 A B s t R y) = (term921 A B s y t R).
Proof. exact (MK_COMB (@lem6998679) (@lem6998678 A B s y t R)). Qed.
Lemma lem6998681 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem6998682 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term922 A B t R y s) = (term923 A B y t R s).
Proof. exact (MK_COMB (@lem6998680 A B s y t R) (@lem6998681 A s)). Qed.
Lemma lem6998683 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term924 A B t R s) = (term925 A B t R s).
Proof. exact (fun_ext (fun y : A -> B => @lem6998682 A B y t R s)). Qed.
Lemma lem6998684 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem6998685 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term913 A B t R s) = (term926 A B t R s).
Proof. exact (MK_COMB (@lem6998684 A B) (@lem6998683 A B t R s)). Qed.
Lemma lem6998686 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : ((term912 A B t R s) = (term913 A B t R s)) = ((term909 A B t R s) = (term926 A B t R s)).
Proof. exact (MK_COMB (@lem6998677 A B t R s) (@lem6998685 A B t R s)). Qed.
Lemma lem6998687 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term909 A B t R s) = (term926 A B t R s).
Proof. exact (EQ_MP (@lem6998686 A B t R s) (@lem6998667 A B t R s)). Qed.
Lemma lem6998688 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term858 A B t R s) = (term926 A B t R s).
Proof. exact (TRANS (@lem6998663 A B t R s) (@lem6998687 A B t R s)). Qed.
Lemma lem6998689 {B : Type'} (t : B -> Prop) (x : B) : (term628 B t x) = (term628 B t x).
Proof. exact (eq_refl (term628 B t x)). Qed.
Lemma lem6998690 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term859 A B x t R s) = (term927 A B x t R s).
Proof. exact (MK_COMB (@lem6998689 B t x) (@lem6998688 A B t R s)). Qed.
Lemma lem6998692 {A : Type'} (P : Prop) (Q : A -> Prop) : (term928 A P Q) = (term929 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem6998693 {A B : Type'} (P : Prop) (Q : type572 A B) : (term930 A B P Q) = (term931 A B P Q).
Proof. exact (@lem6998692 (A -> B) P Q). Qed.
Lemma lem6998694 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term932 A B x t R s) = (term933 A B x t R s).
Proof. exact (@lem6998693 A B (t x) (term925 A B t R s)). Qed.
Lemma lem6998695 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term934 A B t R s y) = (term923 A B y t R s).
Proof. exact (eq_refl (term934 A B t R s y)). Qed.
Lemma lem6998696 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term935 A B t R s) = (term925 A B t R s).
Proof. exact (fun_ext (fun y : A -> B => @lem6998695 A B y t R s)). Qed.
Lemma lem6998697 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem6998698 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term936 A B t R s) = (term926 A B t R s).
Proof. exact (MK_COMB (@lem6998697 A B) (@lem6998696 A B t R s)). Qed.
Lemma lem6998699 {B : Type'} (t : B -> Prop) (x : B) : (term628 B t x) = (term628 B t x).
Proof. exact (eq_refl (term628 B t x)). Qed.
Lemma lem6998700 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term932 A B x t R s) = (term927 A B x t R s).
Proof. exact (MK_COMB (@lem6998699 B t x) (@lem6998698 A B t R s)). Qed.
Lemma lem6998701 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6998702 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term937 A B x t R s) = (term938 A B x t R s).
Proof. exact (MK_COMB (@lem6998701) (@lem6998700 A B x t R s)). Qed.
Lemma lem6998703 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term934 A B t R s y) = (term923 A B y t R s).
Proof. exact (eq_refl (term934 A B t R s y)). Qed.
Lemma lem6998704 {B : Type'} (t : B -> Prop) (x : B) : (term628 B t x) = (term628 B t x).
Proof. exact (eq_refl (term628 B t x)). Qed.
Lemma lem6998705 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term939 A B x t R s y) = (term940 A B x y t R s).
Proof. exact (MK_COMB (@lem6998704 B t x) (@lem6998703 A B y t R s)). Qed.
Lemma lem6998706 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term941 A B x t R s) = (term942 A B x t R s).
Proof. exact (fun_ext (fun y : A -> B => @lem6998705 A B x y t R s)). Qed.
Lemma lem6998707 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem6998708 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term933 A B x t R s) = (term943 A B x t R s).
Proof. exact (MK_COMB (@lem6998707 A B) (@lem6998706 A B x t R s)). Qed.
Lemma lem6998709 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : ((term932 A B x t R s) = (term933 A B x t R s)) = ((term927 A B x t R s) = (term943 A B x t R s)).
Proof. exact (MK_COMB (@lem6998702 A B x t R s) (@lem6998708 A B x t R s)). Qed.
Lemma lem6998710 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term927 A B x t R s) = (term943 A B x t R s).
Proof. exact (EQ_MP (@lem6998709 A B x t R s) (@lem6998694 A B x t R s)). Qed.
Lemma lem6998711 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term859 A B x t R s) = (term943 A B x t R s).
Proof. exact (TRANS (@lem6998690 A B x t R s) (@lem6998710 A B x t R s)). Qed.
Lemma lem6998712 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term838 A B x t R s) = (term943 A B x t R s).
Proof. exact (TRANS (@lem6998578 A B x t R s) (@lem6998711 A B x t R s)). Qed.
Lemma lem6998713 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term639 A B x t R s) = (term943 A B x t R s).
Proof. exact (TRANS (@lem6998318 A B x t R s) (@lem6998712 A B x t R s)). Qed.
Lemma lem6998714 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term639 A B x t R s) : term943 A B x t R s.
Proof. exact (EQ_MP (@lem6998713 A B x t R s) (@lem6998049 A B x t R s h1)). Qed.
Lemma lem6998723 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term944 A B s R x' x) = (term945 A B s R x' x).
Proof. exact (@lem17045 (s x') (R x' x)). Qed.
Lemma lem6998735 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term946 A B s _93304 t R x' x) = (term947 A B s _93304 t R x' x).
Proof. exact (@lem17045 (s x') ((_93304 t R x') = x)). Qed.
Lemma lem6998738 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term731 A B s _93304 t R x' x) = (term731 A B s _93304 t R x' x).
Proof. exact (eq_refl (term731 A B s _93304 t R x' x)). Qed.
Lemma lem6998739 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6998740 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term948 A B s R x' x) = (term949 A B s R x' x).
Proof. exact (MK_COMB (@lem6998739) (@lem6998723 A B s R x' x)). Qed.
Lemma lem6998741 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term950 A B s _93304 t R x' x) = (term951 A B s _93304 t R x' x).
Proof. exact (MK_COMB (@lem6998740 A B s R x' x) (@lem6998738 A B s _93304 t R x' x)). Qed.
Lemma lem6998743 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term952 A B s R x' x) = (term952 A B s R x' x).
Proof. exact (eq_refl (term952 A B s R x' x)). Qed.
Lemma lem6998744 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term953 A B s _93304 t R x' x) = (term954 A B s _93304 t R x' x).
Proof. exact (MK_COMB (@lem6998743 A B s R x' x) (@lem6998735 A B s _93304 t R x' x)). Qed.
Lemma lem6998745 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6998746 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term955 A B s _93304 t R x' x) = (term956 A B s _93304 t R x' x).
Proof. exact (MK_COMB (@lem6998745) (@lem6998744 A B s _93304 t R x' x)). Qed.
Lemma lem6998747 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term957 A B s _93304 t R x' x) = (term958 A B s _93304 t R x' x).
Proof. exact (MK_COMB (@lem6998746 A B s _93304 t R x' x) (@lem6998741 A B s _93304 t R x' x)). Qed.
Lemma lem6998748 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term774 A B s _93304 t R x' x) = (term957 A B s _93304 t R x' x).
Proof. exact (@lem17646 (term660 A B s R x' x) (term731 A B s _93304 t R x' x)). Qed.
Lemma lem6998753 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term774 A B s _93304 t R x' x) = (term958 A B s _93304 t R x' x).
Proof. exact (TRANS (@lem6998748 A B s _93304 t R x' x) (@lem6998747 A B s _93304 t R x' x)). Qed.
Lemma lem6998754 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term774 A B s _93304 t R x' x) : term958 A B s _93304 t R x' x.
Proof. exact (EQ_MP (@lem6998753 A B s _93304 t R x' x) (@lem6998054 A B s _93304 t R x' x h1)). Qed.
Lemma lem6998755 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term940 A B x y t R s.
Proof. exact (h1). Qed.
Lemma lem6998766 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6998767 {A B : Type'} (f : type830 A B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) f x).
Proof. exact (@lem6998766 (B -> Prop) (type467 A B) f x). Qed.
Lemma lem6998768 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) : (_93304 t) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _93304 t).
Proof. exact (@lem6998767 A B _93304 t). Qed.
Lemma lem6998769 {A B : Type'} (R : type1413 A B) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem6998770 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (_93304 t R) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _93304 t R).
Proof. exact (MK_COMB (@lem6998768 A B _93304 t) (@lem6998769 A B R)). Qed.
Lemma lem6998772 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6998773 {A B : Type'} (f : type467 A B) (x : type1413 A B) : (f x) = (@I ((A -> B -> Prop) -> A -> B) f x).
Proof. exact (@lem6998772 (type1413 A B) (A -> B) f x). Qed.
Lemma lem6998774 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _93304 t R) = (term365 A B _93304 t R).
Proof. exact (@lem6998773 A B (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _93304 t) R). Qed.
Lemma lem6998775 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (_93304 t R) = (term365 A B _93304 t R).
Proof. exact (TRANS (@lem6998770 A B _93304 t R) (@lem6998774 A B _93304 t R)). Qed.
Lemma lem6998776 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6998777 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (_93304 t R x) = (term366 A B _93304 t R x).
Proof. exact (MK_COMB (@lem6998775 A B _93304 t R) (@lem6998776 A x)). Qed.
Lemma lem6998779 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6998780 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6998779 A B f x). Qed.
Lemma lem6998781 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term366 A B _93304 t R x) = (term367 A B _93304 t R x).
Proof. exact (@lem6998780 A B (term365 A B _93304 t R) x). Qed.
Lemma lem6998783 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (_93304 t R x) = (term367 A B _93304 t R x).
Proof. exact (TRANS (@lem6998777 A B _93304 t R x) (@lem6998781 A B _93304 t R x)). Qed.
Lemma lem6998784 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (R x).
Proof. exact (eq_refl (R x)). Qed.
Lemma lem6998785 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term161 A B _93304 t R x) = (term368 A B _93304 t R x).
Proof. exact (MK_COMB (@lem6998784 A B R x) (@lem6998783 A B _93304 t R x)). Qed.
Lemma lem6998787 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6998788 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem6998787 A (B -> Prop) f x). Qed.
Lemma lem6998789 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (@I (A -> B -> Prop) R x).
Proof. exact (@lem6998788 A B R x). Qed.
Lemma lem6998790 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term367 A B _93304 t R x) = (term367 A B _93304 t R x).
Proof. exact (eq_refl (term367 A B _93304 t R x)). Qed.
Lemma lem6998791 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term368 A B _93304 t R x) = (term369 A B _93304 t R x).
Proof. exact (MK_COMB (@lem6998789 A B R x) (@lem6998790 A B _93304 t R x)). Qed.
Lemma lem6998793 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6998794 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem6998793 B Prop f x). Qed.
Lemma lem6998795 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term369 A B _93304 t R x) = (term370 A B _93304 t R x).
Proof. exact (@lem6998794 B (@I (A -> B -> Prop) R x) (term367 A B _93304 t R x)). Qed.
Lemma lem6998796 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term368 A B _93304 t R x) = (term370 A B _93304 t R x).
Proof. exact (TRANS (@lem6998791 A B _93304 t R x) (@lem6998795 A B _93304 t R x)). Qed.
Lemma lem6998797 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term161 A B _93304 t R x) = (term370 A B _93304 t R x).
Proof. exact (TRANS (@lem6998785 A B _93304 t R x) (@lem6998796 A B _93304 t R x)). Qed.
Lemma lem6998798 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem6998807 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6998808 {A B : Type'} (f : type830 A B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) f x).
Proof. exact (@lem6998807 (B -> Prop) (type467 A B) f x). Qed.
Lemma lem6998809 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) : (_93304 t) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _93304 t).
Proof. exact (@lem6998808 A B _93304 t). Qed.
Lemma lem6998810 {A B : Type'} (R : type1413 A B) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem6998811 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (_93304 t R) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _93304 t R).
Proof. exact (MK_COMB (@lem6998809 A B _93304 t) (@lem6998810 A B R)). Qed.
Lemma lem6998813 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6998814 {A B : Type'} (f : type467 A B) (x : type1413 A B) : (f x) = (@I ((A -> B -> Prop) -> A -> B) f x).
Proof. exact (@lem6998813 (type1413 A B) (A -> B) f x). Qed.
Lemma lem6998815 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _93304 t R) = (term365 A B _93304 t R).
Proof. exact (@lem6998814 A B (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _93304 t) R). Qed.
Lemma lem6998816 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (_93304 t R) = (term365 A B _93304 t R).
Proof. exact (TRANS (@lem6998811 A B _93304 t R) (@lem6998815 A B _93304 t R)). Qed.
Lemma lem6998817 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6998818 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (_93304 t R x) = (term366 A B _93304 t R x).
Proof. exact (MK_COMB (@lem6998816 A B _93304 t R) (@lem6998817 A x)). Qed.
Lemma lem6998820 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6998821 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6998820 A B f x). Qed.
Lemma lem6998822 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term366 A B _93304 t R x) = (term367 A B _93304 t R x).
Proof. exact (@lem6998821 A B (term365 A B _93304 t R) x). Qed.
Lemma lem6998824 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (_93304 t R x) = (term367 A B _93304 t R x).
Proof. exact (TRANS (@lem6998818 A B _93304 t R x) (@lem6998822 A B _93304 t R x)). Qed.
Lemma lem6998825 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term712 A B _93304 t R x) = (term959 A B _93304 t R x).
Proof. exact (MK_COMB (@lem6998798 B t) (@lem6998824 A B _93304 t R x)). Qed.
Lemma lem6998827 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6998828 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem6998827 B Prop f x). Qed.
Lemma lem6998829 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term959 A B _93304 t R x) = (term960 A B _93304 t R x).
Proof. exact (@lem6998828 B t (term367 A B _93304 t R x)). Qed.
Lemma lem6998830 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term712 A B _93304 t R x) = (term960 A B _93304 t R x).
Proof. exact (TRANS (@lem6998825 A B _93304 t R x) (@lem6998829 A B _93304 t R x)). Qed.
Lemma lem6998831 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6998832 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term714 A B _93304 t R x) = (term961 A B _93304 t R x).
Proof. exact (MK_COMB (@lem6998831) (@lem6998830 A B _93304 t R x)). Qed.
Lemma lem6998833 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term716 A B _93304 t R x) = (term962 A B _93304 t R x).
Proof. exact (MK_COMB (@lem6998832 A B _93304 t R x) (@lem6998797 A B _93304 t R x)). Qed.
Lemma lem6998834 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6998841 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6998842 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem6998841 A (B -> Prop) f x). Qed.
Lemma lem6998843 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (@I (A -> B -> Prop) R x).
Proof. exact (@lem6998842 A B R x). Qed.
Lemma lem6998844 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6998845 {A B : Type'} (R : type1413 A B) (x : A) (x' : B) : (R x x') = (@I (A -> B -> Prop) R x x').
Proof. exact (MK_COMB (@lem6998843 A B R x) (@lem6998844 B x')). Qed.
Lemma lem6998847 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6998848 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem6998847 B Prop f x). Qed.
Lemma lem6998849 {A B : Type'} (R : type1413 A B) (x : A) (x' : B) : (@I (A -> B -> Prop) R x x') = (term378 A B R x x').
Proof. exact (@lem6998848 B (@I (A -> B -> Prop) R x) x'). Qed.
Lemma lem6998851 {A B : Type'} (R : type1413 A B) (x : A) (x' : B) : (R x x') = (term378 A B R x x').
Proof. exact (TRANS (@lem6998845 A B R x x') (@lem6998849 A B R x x')). Qed.
Lemma lem6998852 {A B : Type'} (R : type1413 A B) (x : A) (x' : B) : (term379 A B R x x') = (term380 A B R x x').
Proof. exact (MK_COMB (@lem6998834) (@lem6998851 A B R x x')). Qed.
Lemma lem6998853 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6998858 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6998859 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem6998858 B Prop f x). Qed.
Lemma lem6998861 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (@I (B -> Prop) t x).
Proof. exact (@lem6998859 B t x). Qed.
Lemma lem6998862 {B : Type'} (t : B -> Prop) (x : B) : (term874 B t x) = (term963 B t x).
Proof. exact (MK_COMB (@lem6998853) (@lem6998861 B t x)). Qed.
Lemma lem6998863 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6998864 {B : Type'} (t : B -> Prop) (x : B) : (term831 B t x) = (term964 B t x).
Proof. exact (MK_COMB (@lem6998863) (@lem6998862 B t x)). Qed.
Lemma lem6998865 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term776 A B t R x x') = (term965 A B t R x x').
Proof. exact (MK_COMB (@lem6998864 B t x') (@lem6998852 A B R x x')). Qed.
Lemma lem6998866 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term791 A B t R x) = (term966 A B t R x).
Proof. exact (fun_ext (fun x' : B => @lem6998865 A B t R x x')). Qed.
Lemma lem6998867 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6998868 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term800 A B t R x) = (term967 A B t R x).
Proof. exact (MK_COMB (@lem6998867 B) (@lem6998866 A B t R x)). Qed.
Lemma lem6998869 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6998870 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term802 A B t R x) = (term968 A B t R x).
Proof. exact (MK_COMB (@lem6998869) (@lem6998868 A B t R x)). Qed.
Lemma lem6998871 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term803 A B _93304 t R x) = (term969 A B _93304 t R x).
Proof. exact (MK_COMB (@lem6998870 A B t R x) (@lem6998833 A B _93304 t R x)). Qed.
Lemma lem6998872 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term804 A B _93304 t R) = (term970 A B _93304 t R).
Proof. exact (fun_ext (fun x : A => @lem6998871 A B _93304 t R x)). Qed.
Lemma lem6998873 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6998874 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term805 A B _93304 t R) = (term971 A B _93304 t R).
Proof. exact (MK_COMB (@lem6998873 A) (@lem6998872 A B _93304 t R)). Qed.
Lemma lem6998875 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) : (term806 A B _93304 t) = (term972 A B _93304 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem6998874 A B _93304 t R)). Qed.
Lemma lem6998876 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem6998877 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) : (term807 A B _93304 t) = (term973 A B _93304 t).
Proof. exact (MK_COMB (@lem6998876 A B) (@lem6998875 A B _93304 t)). Qed.
Lemma lem6998878 {A B : Type'} (_93304 : type830 A B) : (term808 A B _93304) = (term974 A B _93304).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6998877 A B _93304 t)). Qed.
Lemma lem6998879 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6998880 {A B : Type'} (_93304 : type830 A B) : (term809 A B _93304) = (term975 A B _93304).
Proof. exact (MK_COMB (@lem6998879 B) (@lem6998878 A B _93304)). Qed.
Lemma lem6998881 {A B : Type'} (_93304 : type830 A B) (h1 : term728 A B _93304) : term975 A B _93304.
Proof. exact (EQ_MP (@lem6998880 A B _93304) (@lem6998256 A B _93304 h1)). Qed.
Lemma lem6998882 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6998891 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6998892 {A B : Type'} (f : type830 A B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) f x).
Proof. exact (@lem6998891 (B -> Prop) (type467 A B) f x). Qed.
Lemma lem6998893 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) : (_93304 t) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _93304 t).
Proof. exact (@lem6998892 A B _93304 t). Qed.
Lemma lem6998894 {A B : Type'} (R : type1413 A B) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem6998895 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (_93304 t R) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _93304 t R).
Proof. exact (MK_COMB (@lem6998893 A B _93304 t) (@lem6998894 A B R)). Qed.
Lemma lem6998897 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6998898 {A B : Type'} (f : type467 A B) (x : type1413 A B) : (f x) = (@I ((A -> B -> Prop) -> A -> B) f x).
Proof. exact (@lem6998897 (type1413 A B) (A -> B) f x). Qed.
Lemma lem6998899 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _93304 t R) = (term365 A B _93304 t R).
Proof. exact (@lem6998898 A B (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _93304 t) R). Qed.
Lemma lem6998900 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (_93304 t R) = (term365 A B _93304 t R).
Proof. exact (TRANS (@lem6998895 A B _93304 t R) (@lem6998899 A B _93304 t R)). Qed.
Lemma lem6998901 {A : Type'} (x' : A) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem6998902 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (_93304 t R x') = (term366 A B _93304 t R x').
Proof. exact (MK_COMB (@lem6998900 A B _93304 t R) (@lem6998901 A x')). Qed.
Lemma lem6998904 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6998905 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6998904 A B f x). Qed.
Lemma lem6998906 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term366 A B _93304 t R x') = (term367 A B _93304 t R x').
Proof. exact (@lem6998905 A B (term365 A B _93304 t R) x'). Qed.
Lemma lem6998908 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (_93304 t R x') = (term367 A B _93304 t R x').
Proof. exact (TRANS (@lem6998902 A B _93304 t R x') (@lem6998906 A B _93304 t R x')). Qed.
Lemma lem6998909 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6998910 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term149 A B _93304 t R x') = (term976 A B _93304 t R x').
Proof. exact (MK_COMB (@lem6998882 B) (@lem6998908 A B _93304 t R x')). Qed.
Lemma lem6998911 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : ((_93304 t R x') = x) = ((term367 A B _93304 t R x') = x).
Proof. exact (MK_COMB (@lem6998910 A B _93304 t R x') (@lem6998909 B x)). Qed.
Lemma lem6998916 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6998917 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem6998916 A Prop f x). Qed.
Lemma lem6998919 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (@I (A -> Prop) s x').
Proof. exact (@lem6998917 A s x'). Qed.
Lemma lem6998920 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6998921 {A : Type'} (s : A -> Prop) (x' : A) : (term628 A s x') = (term977 A s x').
Proof. exact (MK_COMB (@lem6998920) (@lem6998919 A s x')). Qed.
Lemma lem6998922 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term731 A B s _93304 t R x' x) = (term978 A B s _93304 t R x' x).
Proof. exact (MK_COMB (@lem6998921 A s x') (@lem6998911 A B _93304 t R x' x)). Qed.
Lemma lem6998923 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6998930 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6998931 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem6998930 A (B -> Prop) f x). Qed.
Lemma lem6998932 {A B : Type'} (R : type1413 A B) (x' : A) : (R x') = (@I (A -> B -> Prop) R x').
Proof. exact (@lem6998931 A B R x'). Qed.
Lemma lem6998933 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6998934 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) : (R x' x) = (@I (A -> B -> Prop) R x' x).
Proof. exact (MK_COMB (@lem6998932 A B R x') (@lem6998933 B x)). Qed.
Lemma lem6998936 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6998937 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem6998936 B Prop f x). Qed.
Lemma lem6998938 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) : (@I (A -> B -> Prop) R x' x) = (term378 A B R x' x).
Proof. exact (@lem6998937 B (@I (A -> B -> Prop) R x') x). Qed.
Lemma lem6998940 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) : (R x' x) = (term378 A B R x' x).
Proof. exact (TRANS (@lem6998934 A B R x' x) (@lem6998938 A B R x' x)). Qed.
Lemma lem6998941 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) : (term379 A B R x' x) = (term380 A B R x' x).
Proof. exact (MK_COMB (@lem6998923) (@lem6998940 A B R x' x)). Qed.
Lemma lem6998942 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6998947 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6998948 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem6998947 A Prop f x). Qed.
Lemma lem6998950 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (@I (A -> Prop) s x').
Proof. exact (@lem6998948 A s x'). Qed.
Lemma lem6998951 {A : Type'} (s : A -> Prop) (x' : A) : (term874 A s x') = (term963 A s x').
Proof. exact (MK_COMB (@lem6998942) (@lem6998950 A s x')). Qed.
Lemma lem6998952 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6998953 {A : Type'} (s : A -> Prop) (x' : A) : (term831 A s x') = (term964 A s x').
Proof. exact (MK_COMB (@lem6998952) (@lem6998951 A s x')). Qed.
Lemma lem6998954 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term945 A B s R x' x) = (term979 A B s R x' x).
Proof. exact (MK_COMB (@lem6998953 A s x') (@lem6998941 A B R x' x)). Qed.
Lemma lem6998955 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6998956 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term949 A B s R x' x) = (term980 A B s R x' x).
Proof. exact (MK_COMB (@lem6998955) (@lem6998954 A B s R x' x)). Qed.
Lemma lem6998957 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term951 A B s _93304 t R x' x) = (term981 A B s _93304 t R x' x).
Proof. exact (MK_COMB (@lem6998956 A B s R x' x) (@lem6998922 A B s _93304 t R x' x)). Qed.
Lemma lem6998958 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6998959 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6998968 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6998969 {A B : Type'} (f : type830 A B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) f x).
Proof. exact (@lem6998968 (B -> Prop) (type467 A B) f x). Qed.
Lemma lem6998970 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) : (_93304 t) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _93304 t).
Proof. exact (@lem6998969 A B _93304 t). Qed.
Lemma lem6998971 {A B : Type'} (R : type1413 A B) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem6998972 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (_93304 t R) = (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _93304 t R).
Proof. exact (MK_COMB (@lem6998970 A B _93304 t) (@lem6998971 A B R)). Qed.
Lemma lem6998974 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6998975 {A B : Type'} (f : type467 A B) (x : type1413 A B) : (f x) = (@I ((A -> B -> Prop) -> A -> B) f x).
Proof. exact (@lem6998974 (type1413 A B) (A -> B) f x). Qed.
Lemma lem6998976 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _93304 t R) = (term365 A B _93304 t R).
Proof. exact (@lem6998975 A B (@I ((B -> Prop) -> (A -> B -> Prop) -> A -> B) _93304 t) R). Qed.
Lemma lem6998977 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (_93304 t R) = (term365 A B _93304 t R).
Proof. exact (TRANS (@lem6998972 A B _93304 t R) (@lem6998976 A B _93304 t R)). Qed.
Lemma lem6998978 {A : Type'} (x' : A) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem6998979 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (_93304 t R x') = (term366 A B _93304 t R x').
Proof. exact (MK_COMB (@lem6998977 A B _93304 t R) (@lem6998978 A x')). Qed.
Lemma lem6998981 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6998982 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6998981 A B f x). Qed.
Lemma lem6998983 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term366 A B _93304 t R x') = (term367 A B _93304 t R x').
Proof. exact (@lem6998982 A B (term365 A B _93304 t R) x'). Qed.
Lemma lem6998985 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (_93304 t R x') = (term367 A B _93304 t R x').
Proof. exact (TRANS (@lem6998979 A B _93304 t R x') (@lem6998983 A B _93304 t R x')). Qed.
Lemma lem6998986 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6998987 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term149 A B _93304 t R x') = (term976 A B _93304 t R x').
Proof. exact (MK_COMB (@lem6998959 B) (@lem6998985 A B _93304 t R x')). Qed.
Lemma lem6998988 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : ((_93304 t R x') = x) = ((term367 A B _93304 t R x') = x).
Proof. exact (MK_COMB (@lem6998987 A B _93304 t R x') (@lem6998986 B x)). Qed.
Lemma lem6998989 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term982 A B _93304 t R x' x) = (term983 A B _93304 t R x' x).
Proof. exact (MK_COMB (@lem6998958) (@lem6998988 A B _93304 t R x' x)). Qed.
Lemma lem6998990 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6998995 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6998996 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem6998995 A Prop f x). Qed.
Lemma lem6998998 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (@I (A -> Prop) s x').
Proof. exact (@lem6998996 A s x'). Qed.
Lemma lem6998999 {A : Type'} (s : A -> Prop) (x' : A) : (term874 A s x') = (term963 A s x').
Proof. exact (MK_COMB (@lem6998990) (@lem6998998 A s x')). Qed.
Lemma lem6999000 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6999001 {A : Type'} (s : A -> Prop) (x' : A) : (term831 A s x') = (term964 A s x').
Proof. exact (MK_COMB (@lem6999000) (@lem6998999 A s x')). Qed.
Lemma lem6999002 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term947 A B s _93304 t R x' x) = (term984 A B s _93304 t R x' x).
Proof. exact (MK_COMB (@lem6999001 A s x') (@lem6998989 A B _93304 t R x' x)). Qed.
Lemma lem6999009 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6999010 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem6999009 A (B -> Prop) f x). Qed.
Lemma lem6999011 {A B : Type'} (R : type1413 A B) (x' : A) : (R x') = (@I (A -> B -> Prop) R x').
Proof. exact (@lem6999010 A B R x'). Qed.
Lemma lem6999012 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6999013 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) : (R x' x) = (@I (A -> B -> Prop) R x' x).
Proof. exact (MK_COMB (@lem6999011 A B R x') (@lem6999012 B x)). Qed.
Lemma lem6999015 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6999016 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem6999015 B Prop f x). Qed.
Lemma lem6999017 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) : (@I (A -> B -> Prop) R x' x) = (term378 A B R x' x).
Proof. exact (@lem6999016 B (@I (A -> B -> Prop) R x') x). Qed.
Lemma lem6999019 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) : (R x' x) = (term378 A B R x' x).
Proof. exact (TRANS (@lem6999013 A B R x' x) (@lem6999017 A B R x' x)). Qed.
Lemma lem6999024 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6999025 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem6999024 A Prop f x). Qed.
Lemma lem6999027 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (@I (A -> Prop) s x').
Proof. exact (@lem6999025 A s x'). Qed.
Lemma lem6999028 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6999029 {A : Type'} (s : A -> Prop) (x' : A) : (term628 A s x') = (term977 A s x').
Proof. exact (MK_COMB (@lem6999028) (@lem6999027 A s x')). Qed.
Lemma lem6999030 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term660 A B s R x' x) = (term985 A B s R x' x).
Proof. exact (MK_COMB (@lem6999029 A s x') (@lem6999019 A B R x' x)). Qed.
Lemma lem6999031 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6999032 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term952 A B s R x' x) = (term986 A B s R x' x).
Proof. exact (MK_COMB (@lem6999031) (@lem6999030 A B s R x' x)). Qed.
Lemma lem6999033 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term954 A B s _93304 t R x' x) = (term987 A B s _93304 t R x' x).
Proof. exact (MK_COMB (@lem6999032 A B s R x' x) (@lem6999002 A B s _93304 t R x' x)). Qed.
Lemma lem6999034 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6999035 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term956 A B s _93304 t R x' x) = (term988 A B s _93304 t R x' x).
Proof. exact (MK_COMB (@lem6999034) (@lem6999033 A B s _93304 t R x' x)). Qed.
Lemma lem6999036 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term958 A B s _93304 t R x' x) = (term989 A B s _93304 t R x' x).
Proof. exact (MK_COMB (@lem6999035 A B s _93304 t R x' x) (@lem6998957 A B s _93304 t R x' x)). Qed.
Lemma lem6999037 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term774 A B s _93304 t R x' x) : term989 A B s _93304 t R x' x.
Proof. exact (EQ_MP (@lem6999036 A B s _93304 t R x' x) (@lem6998754 A B s _93304 t R x' x h1)). Qed.
Lemma lem6999042 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6999043 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6999042 (A -> Prop) Prop f x). Qed.
Lemma lem6999045 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem6999043 A (@FINITE A) s). Qed.
Lemma lem6999050 {B : Type'} (y' : B) (y : B) : (y' = y) = (y' = y).
Proof. exact (eq_refl (y' = y)). Qed.
Lemma lem6999051 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6999058 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6999059 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem6999058 A (B -> Prop) f x). Qed.
Lemma lem6999060 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (@I (A -> B -> Prop) R x).
Proof. exact (@lem6999059 A B R x). Qed.
Lemma lem6999061 {B : Type'} (y' : B) : y' = y'.
Proof. exact (eq_refl y'). Qed.
Lemma lem6999062 {A B : Type'} (R : type1413 A B) (x : A) (y' : B) : (R x y') = (@I (A -> B -> Prop) R x y').
Proof. exact (MK_COMB (@lem6999060 A B R x) (@lem6999061 B y')). Qed.
Lemma lem6999064 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6999065 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem6999064 B Prop f x). Qed.
Lemma lem6999066 {A B : Type'} (R : type1413 A B) (x : A) (y' : B) : (@I (A -> B -> Prop) R x y') = (term378 A B R x y').
Proof. exact (@lem6999065 B (@I (A -> B -> Prop) R x) y'). Qed.
Lemma lem6999068 {A B : Type'} (R : type1413 A B) (x : A) (y' : B) : (R x y') = (term378 A B R x y').
Proof. exact (TRANS (@lem6999062 A B R x y') (@lem6999066 A B R x y')). Qed.
Lemma lem6999069 {A B : Type'} (R : type1413 A B) (x : A) (y' : B) : (term379 A B R x y') = (term380 A B R x y').
Proof. exact (MK_COMB (@lem6999051) (@lem6999068 A B R x y')). Qed.
Lemma lem6999070 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6999075 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6999076 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem6999075 B Prop f x). Qed.
Lemma lem6999078 {B : Type'} (t : B -> Prop) (y' : B) : (t y') = (@I (B -> Prop) t y').
Proof. exact (@lem6999076 B t y'). Qed.
Lemma lem6999079 {B : Type'} (t : B -> Prop) (y' : B) : (term874 B t y') = (term963 B t y').
Proof. exact (MK_COMB (@lem6999070) (@lem6999078 B t y')). Qed.
Lemma lem6999080 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6999081 {B : Type'} (t : B -> Prop) (y' : B) : (term831 B t y') = (term964 B t y').
Proof. exact (MK_COMB (@lem6999080) (@lem6999079 B t y')). Qed.
Lemma lem6999082 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term776 A B t R x y') = (term965 A B t R x y').
Proof. exact (MK_COMB (@lem6999081 B t y') (@lem6999069 A B R x y')). Qed.
Lemma lem6999083 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6999084 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term778 A B t R x y') = (term990 A B t R x y').
Proof. exact (MK_COMB (@lem6999083) (@lem6999082 A B t R x y')). Qed.
Lemma lem6999085 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term814 A B t R x y' y) = (term991 A B t R x y' y).
Proof. exact (MK_COMB (@lem6999084 A B t R x y') (@lem6999050 B y' y)). Qed.
Lemma lem6999086 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term841 A B t R x y) = (term992 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem6999085 A B t R x y' y)). Qed.
Lemma lem6999087 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6999088 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term849 A B t R x y) = (term993 A B t R x y).
Proof. exact (MK_COMB (@lem6999087 B) (@lem6999086 A B t R x y)). Qed.
Lemma lem6999089 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6999096 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6999097 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem6999096 A (B -> Prop) f x). Qed.
Lemma lem6999098 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (@I (A -> B -> Prop) R x).
Proof. exact (@lem6999097 A B R x). Qed.
Lemma lem6999099 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6999100 {A B : Type'} (R : type1413 A B) (x : A) (y : B) : (R x y) = (@I (A -> B -> Prop) R x y).
Proof. exact (MK_COMB (@lem6999098 A B R x) (@lem6999099 B y)). Qed.
Lemma lem6999102 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6999103 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem6999102 B Prop f x). Qed.
Lemma lem6999104 {A B : Type'} (R : type1413 A B) (x : A) (y : B) : (@I (A -> B -> Prop) R x y) = (term378 A B R x y).
Proof. exact (@lem6999103 B (@I (A -> B -> Prop) R x) y). Qed.
Lemma lem6999106 {A B : Type'} (R : type1413 A B) (x : A) (y : B) : (R x y) = (term378 A B R x y).
Proof. exact (TRANS (@lem6999100 A B R x y) (@lem6999104 A B R x y)). Qed.
Lemma lem6999107 {A B : Type'} (R : type1413 A B) (x : A) (y : B) : (term379 A B R x y) = (term380 A B R x y).
Proof. exact (MK_COMB (@lem6999089) (@lem6999106 A B R x y)). Qed.
Lemma lem6999108 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6999113 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6999114 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem6999113 B Prop f x). Qed.
Lemma lem6999116 {B : Type'} (t : B -> Prop) (y : B) : (t y) = (@I (B -> Prop) t y).
Proof. exact (@lem6999114 B t y). Qed.
Lemma lem6999117 {B : Type'} (t : B -> Prop) (y : B) : (term874 B t y) = (term963 B t y).
Proof. exact (MK_COMB (@lem6999108) (@lem6999116 B t y)). Qed.
Lemma lem6999118 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6999119 {B : Type'} (t : B -> Prop) (y : B) : (term831 B t y) = (term964 B t y).
Proof. exact (MK_COMB (@lem6999118) (@lem6999117 B t y)). Qed.
Lemma lem6999120 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term776 A B t R x y) = (term965 A B t R x y).
Proof. exact (MK_COMB (@lem6999119 B t y) (@lem6999107 A B R x y)). Qed.
Lemma lem6999121 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6999122 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term778 A B t R x y) = (term990 A B t R x y).
Proof. exact (MK_COMB (@lem6999121) (@lem6999120 A B t R x y)). Qed.
Lemma lem6999123 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term850 A B t R x y) = (term994 A B t R x y).
Proof. exact (MK_COMB (@lem6999122 A B t R x y) (@lem6999088 A B t R x y)). Qed.
Lemma lem6999124 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term851 A B t R x) = (term995 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem6999123 A B t R x y)). Qed.
Lemma lem6999125 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6999126 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term852 A B t R x) = (term996 A B t R x).
Proof. exact (MK_COMB (@lem6999125 B) (@lem6999124 A B t R x)). Qed.
Lemma lem6999133 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6999134 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6999133 A B f x). Qed.
Lemma lem6999136 {A B : Type'} (y : A -> B) (x : A) : (y x) = (@I (A -> B) y x).
Proof. exact (@lem6999134 A B y x). Qed.
Lemma lem6999137 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (R x).
Proof. exact (eq_refl (R x)). Qed.
Lemma lem6999138 {A B : Type'} (R : type1413 A B) (y : A -> B) (x : A) : (term403 A B R y x) = (term404 A B R y x).
Proof. exact (MK_COMB (@lem6999137 A B R x) (@lem6999136 A B y x)). Qed.
Lemma lem6999140 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6999141 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem6999140 A (B -> Prop) f x). Qed.
Lemma lem6999142 {A B : Type'} (R : type1413 A B) (x : A) : (R x) = (@I (A -> B -> Prop) R x).
Proof. exact (@lem6999141 A B R x). Qed.
Lemma lem6999143 {A B : Type'} (y : A -> B) (x : A) : (@I (A -> B) y x) = (@I (A -> B) y x).
Proof. exact (eq_refl (@I (A -> B) y x)). Qed.
Lemma lem6999144 {A B : Type'} (R : type1413 A B) (y : A -> B) (x : A) : (term404 A B R y x) = (term405 A B R y x).
Proof. exact (MK_COMB (@lem6999142 A B R x) (@lem6999143 A B y x)). Qed.
Lemma lem6999146 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6999147 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem6999146 B Prop f x). Qed.
Lemma lem6999148 {A B : Type'} (R : type1413 A B) (y : A -> B) (x : A) : (term405 A B R y x) = (term406 A B R y x).
Proof. exact (@lem6999147 B (@I (A -> B -> Prop) R x) (@I (A -> B) y x)). Qed.
Lemma lem6999149 {A B : Type'} (R : type1413 A B) (y : A -> B) (x : A) : (term404 A B R y x) = (term406 A B R y x).
Proof. exact (TRANS (@lem6999144 A B R y x) (@lem6999148 A B R y x)). Qed.
Lemma lem6999150 {A B : Type'} (R : type1413 A B) (y : A -> B) (x : A) : (term403 A B R y x) = (term406 A B R y x).
Proof. exact (TRANS (@lem6999138 A B R y x) (@lem6999149 A B R y x)). Qed.
Lemma lem6999151 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem6999156 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6999157 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6999156 A B f x). Qed.
Lemma lem6999159 {A B : Type'} (y : A -> B) (x : A) : (y x) = (@I (A -> B) y x).
Proof. exact (@lem6999157 A B y x). Qed.
Lemma lem6999160 {A B : Type'} (t : B -> Prop) (y : A -> B) (x : A) : (term997 A B t y x) = (term998 A B t y x).
Proof. exact (MK_COMB (@lem6999151 B t) (@lem6999159 A B y x)). Qed.
Lemma lem6999162 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6999163 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem6999162 B Prop f x). Qed.
Lemma lem6999164 {A B : Type'} (t : B -> Prop) (y : A -> B) (x : A) : (term998 A B t y x) = (term999 A B t y x).
Proof. exact (@lem6999163 B t (@I (A -> B) y x)). Qed.
Lemma lem6999165 {A B : Type'} (t : B -> Prop) (y : A -> B) (x : A) : (term997 A B t y x) = (term999 A B t y x).
Proof. exact (TRANS (@lem6999160 A B t y x) (@lem6999164 A B t y x)). Qed.
Lemma lem6999166 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6999167 {A B : Type'} (t : B -> Prop) (y : A -> B) (x : A) : (term1000 A B t y x) = (term1001 A B t y x).
Proof. exact (MK_COMB (@lem6999166) (@lem6999165 A B t y x)). Qed.
Lemma lem6999168 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1002 A B t R y x) = (term1003 A B t R y x).
Proof. exact (MK_COMB (@lem6999167 A B t y x) (@lem6999150 A B R y x)). Qed.
Lemma lem6999169 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6999170 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1004 A B t R y x) = (term1005 A B t R y x).
Proof. exact (MK_COMB (@lem6999169) (@lem6999168 A B t R y x)). Qed.
Lemma lem6999171 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1006 A B y t R x) = (term1007 A B y t R x).
Proof. exact (MK_COMB (@lem6999170 A B t R y x) (@lem6999126 A B t R x)). Qed.
Lemma lem6999172 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6999177 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6999178 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem6999177 A Prop f x). Qed.
Lemma lem6999180 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem6999178 A s x). Qed.
Lemma lem6999181 {A : Type'} (s : A -> Prop) (x : A) : (term874 A s x) = (term963 A s x).
Proof. exact (MK_COMB (@lem6999172) (@lem6999180 A s x)). Qed.
Lemma lem6999182 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6999183 {A : Type'} (s : A -> Prop) (x : A) : (term831 A s x) = (term964 A s x).
Proof. exact (MK_COMB (@lem6999182) (@lem6999181 A s x)). Qed.
Lemma lem6999184 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term900 A B s y t R x) = (term1008 A B s y t R x).
Proof. exact (MK_COMB (@lem6999183 A s x) (@lem6999171 A B y t R x)). Qed.
Lemma lem6999185 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term902 A B s y t R) = (term1009 A B s y t R).
Proof. exact (fun_ext (fun x : A => @lem6999184 A B s y t R x)). Qed.
Lemma lem6999186 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6999187 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term904 A B s y t R) = (term1010 A B s y t R).
Proof. exact (MK_COMB (@lem6999186 A) (@lem6999185 A B s y t R)). Qed.
Lemma lem6999188 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6999189 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term921 A B s y t R) = (term1011 A B s y t R).
Proof. exact (MK_COMB (@lem6999188) (@lem6999187 A B s y t R)). Qed.
Lemma lem6999190 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term923 A B y t R s) = (term1012 A B y t R s).
Proof. exact (MK_COMB (@lem6999189 A B s y t R) (@lem6999045 A s)). Qed.
Lemma lem6999195 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6999196 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem6999195 B Prop f x). Qed.
Lemma lem6999198 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (@I (B -> Prop) t x).
Proof. exact (@lem6999196 B t x). Qed.
Lemma lem6999199 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6999200 {B : Type'} (t : B -> Prop) (x : B) : (term628 B t x) = (term977 B t x).
Proof. exact (MK_COMB (@lem6999199) (@lem6999198 B t x)). Qed.
Lemma lem6999201 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) : (term940 A B x y t R s) = (term1013 A B x y t R s).
Proof. exact (MK_COMB (@lem6999200 B t x) (@lem6999190 A B y t R s)). Qed.
Lemma lem6999202 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1013 A B x y t R s.
Proof. exact (EQ_MP (@lem6999201 A B x y t R s) (@lem6998755 A B x y t R s h1)). Qed.
Lemma lem6999203 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1012 A B y t R s.
Proof. exact (proj2 (@lem6999202 A B x y t R s h1)). Qed.
Lemma lem6999206 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1010 A B s y t R.
Proof. exact (proj1 (@lem6999203 A B x y t R s h1)). Qed.
Lemma lem6999207 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _93304 t R x' x) : term987 A B s _93304 t R x' x.
Proof. exact (h1). Qed.
Lemma lem6999208 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _93304 t R x' x) : term981 A B s _93304 t R x' x.
Proof. exact (h1). Qed.
Lemma lem6999209 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _93304 t R x' x) : term984 A B s _93304 t R x' x.
Proof. exact (proj2 (@lem6999207 A B s _93304 t R x' x h1)). Qed.
Lemma lem6999210 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _93304 t R x' x) : term985 A B s R x' x.
Proof. exact (proj1 (@lem6999207 A B s _93304 t R x' x h1)). Qed.
Lemma lem6999215 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _93304 t R x' x) : term978 A B s _93304 t R x' x.
Proof. exact (proj2 (@lem6999208 A B s _93304 t R x' x h1)). Qed.
Lemma lem6999216 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _93304 t R x' x) : term979 A B s R x' x.
Proof. exact (proj1 (@lem6999208 A B s _93304 t R x' x h1)). Qed.
Lemma lem6999492 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term963 A s x') : term963 A s x'.
Proof. exact (h1). Qed.
Lemma lem6999494 {A : Type'} (P : A -> Prop) (Q : Prop) : (term242 A P Q) = (term241 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem6999495 {B : Type'} (P : B -> Prop) (Q : Prop) : (term242 B P Q) = (term241 B P Q).
Proof. exact (@lem6999494 B P Q). Qed.
Lemma lem6999496 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1014 A B _93304 t R x) = (term1015 A B _93304 t R x).
Proof. exact (@lem6999495 B (term966 A B t R x) (term962 A B _93304 t R x)). Qed.
Lemma lem6999497 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term1016 A B t R x x') = (term965 A B t R x x').
Proof. exact (eq_refl (term1016 A B t R x x')). Qed.
Lemma lem6999498 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term1017 A B t R x) = (term966 A B t R x).
Proof. exact (fun_ext (fun x' : B => @lem6999497 A B t R x x')). Qed.
Lemma lem6999499 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6999500 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term1018 A B t R x) = (term967 A B t R x).
Proof. exact (MK_COMB (@lem6999499 B) (@lem6999498 A B t R x)). Qed.
Lemma lem6999501 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6999502 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term1019 A B t R x) = (term968 A B t R x).
Proof. exact (MK_COMB (@lem6999501) (@lem6999500 A B t R x)). Qed.
Lemma lem6999503 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term962 A B _93304 t R x) = (term962 A B _93304 t R x).
Proof. exact (eq_refl (term962 A B _93304 t R x)). Qed.
Lemma lem6999504 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1014 A B _93304 t R x) = (term969 A B _93304 t R x).
Proof. exact (MK_COMB (@lem6999502 A B t R x) (@lem6999503 A B _93304 t R x)). Qed.
Lemma lem6999505 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6999506 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1020 A B _93304 t R x) = (term1021 A B _93304 t R x).
Proof. exact (MK_COMB (@lem6999505) (@lem6999504 A B _93304 t R x)). Qed.
Lemma lem6999507 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term1016 A B t R x x') = (term965 A B t R x x').
Proof. exact (eq_refl (term1016 A B t R x x')). Qed.
Lemma lem6999508 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6999509 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term1022 A B t R x x') = (term990 A B t R x x').
Proof. exact (MK_COMB (@lem6999508) (@lem6999507 A B t R x x')). Qed.
Lemma lem6999510 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term962 A B _93304 t R x) = (term962 A B _93304 t R x).
Proof. exact (eq_refl (term962 A B _93304 t R x)). Qed.
Lemma lem6999511 {A B : Type'} (x : B) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term1023 A B x _93304 t R x') = (term1024 A B x _93304 t R x').
Proof. exact (MK_COMB (@lem6999509 A B t R x' x) (@lem6999510 A B _93304 t R x')). Qed.
Lemma lem6999512 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1025 A B _93304 t R x) = (term1026 A B _93304 t R x).
Proof. exact (fun_ext (fun x' : B => @lem6999511 A B x' _93304 t R x)). Qed.
Lemma lem6999513 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6999514 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1015 A B _93304 t R x) = (term1027 A B _93304 t R x).
Proof. exact (MK_COMB (@lem6999513 B) (@lem6999512 A B _93304 t R x)). Qed.
Lemma lem6999515 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : ((term1014 A B _93304 t R x) = (term1015 A B _93304 t R x)) = ((term969 A B _93304 t R x) = (term1027 A B _93304 t R x)).
Proof. exact (MK_COMB (@lem6999506 A B _93304 t R x) (@lem6999514 A B _93304 t R x)). Qed.
Lemma lem6999516 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term969 A B _93304 t R x) = (term1027 A B _93304 t R x).
Proof. exact (EQ_MP (@lem6999515 A B _93304 t R x) (@lem6999496 A B _93304 t R x)). Qed.
Lemma lem6999517 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term970 A B _93304 t R) = (term1028 A B _93304 t R).
Proof. exact (fun_ext (fun x : A => @lem6999516 A B _93304 t R x)). Qed.
Lemma lem6999518 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6999519 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term971 A B _93304 t R) = (term1029 A B _93304 t R).
Proof. exact (MK_COMB (@lem6999518 A) (@lem6999517 A B _93304 t R)). Qed.
Lemma lem6999520 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) : (term972 A B _93304 t) = (term1030 A B _93304 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem6999519 A B _93304 t R)). Qed.
Lemma lem6999521 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem6999522 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) : (term973 A B _93304 t) = (term1031 A B _93304 t).
Proof. exact (MK_COMB (@lem6999521 A B) (@lem6999520 A B _93304 t)). Qed.
Lemma lem6999523 {A B : Type'} (_93304 : type830 A B) : (term974 A B _93304) = (term1032 A B _93304).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6999522 A B _93304 t)). Qed.
Lemma lem6999524 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6999525 {A B : Type'} (_93304 : type830 A B) : (term975 A B _93304) = (term1033 A B _93304).
Proof. exact (MK_COMB (@lem6999524 B) (@lem6999523 A B _93304)). Qed.
Lemma lem6999548 {A B : Type'} (x : B) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term1024 A B x _93304 t R x') = (term1034 A B x _93304 t R x').
Proof. exact (@lem19490 (term960 A B _93304 t R x') (term965 A B t R x' x) (term370 A B _93304 t R x')). Qed.
Lemma lem6999549 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1026 A B _93304 t R x) = (term1035 A B _93304 t R x).
Proof. exact (fun_ext (fun x' : B => @lem6999548 A B x' _93304 t R x)). Qed.
Lemma lem6999550 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6999551 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1027 A B _93304 t R x) = (term1036 A B _93304 t R x).
Proof. exact (MK_COMB (@lem6999550 B) (@lem6999549 A B _93304 t R x)). Qed.
Lemma lem6999552 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term1028 A B _93304 t R) = (term1037 A B _93304 t R).
Proof. exact (fun_ext (fun x : A => @lem6999551 A B _93304 t R x)). Qed.
Lemma lem6999553 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6999554 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term1029 A B _93304 t R) = (term1038 A B _93304 t R).
Proof. exact (MK_COMB (@lem6999553 A) (@lem6999552 A B _93304 t R)). Qed.
Lemma lem6999555 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) : (term1030 A B _93304 t) = (term1039 A B _93304 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem6999554 A B _93304 t R)). Qed.
Lemma lem6999556 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem6999557 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) : (term1031 A B _93304 t) = (term1040 A B _93304 t).
Proof. exact (MK_COMB (@lem6999556 A B) (@lem6999555 A B _93304 t)). Qed.
Lemma lem6999558 {A B : Type'} (_93304 : type830 A B) : (term1032 A B _93304) = (term1041 A B _93304).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6999557 A B _93304 t)). Qed.
Lemma lem6999559 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6999560 {A B : Type'} (_93304 : type830 A B) : (term1033 A B _93304) = (term1042 A B _93304).
Proof. exact (MK_COMB (@lem6999559 B) (@lem6999558 A B _93304)). Qed.
Lemma lem6999561 {A B : Type'} (_93304 : type830 A B) : (term975 A B _93304) = (term1042 A B _93304).
Proof. exact (TRANS (@lem6999525 A B _93304) (@lem6999560 A B _93304)). Qed.
Lemma lem6999562 {A B : Type'} (_93304 : type830 A B) (h1 : term728 A B _93304) : term1042 A B _93304.
Proof. exact (EQ_MP (@lem6999561 A B _93304) (@lem6998881 A B _93304 h1)). Qed.
Lemma lem6999568 {A : Type'} (P : Prop) (Q : A -> Prop) : (term292 A P Q) = (term291 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem6999569 {B : Type'} (P : Prop) (Q : B -> Prop) : (term292 B P Q) = (term291 B P Q).
Proof. exact (@lem6999568 B P Q). Qed.
Lemma lem6999570 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1043 A B t R x y) = (term1044 A B t R x y).
Proof. exact (@lem6999569 B (term965 A B t R x y) (term992 A B t R x y)). Qed.
Lemma lem6999571 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term1045 A B t R x y y') = (term991 A B t R x y' y).
Proof. exact (eq_refl (term1045 A B t R x y y')). Qed.
Lemma lem6999572 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1046 A B t R x y) = (term992 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem6999571 A B t R x y' y)). Qed.
Lemma lem6999573 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6999574 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1047 A B t R x y) = (term993 A B t R x y).
Proof. exact (MK_COMB (@lem6999573 B) (@lem6999572 A B t R x y)). Qed.
Lemma lem6999575 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term990 A B t R x y) = (term990 A B t R x y).
Proof. exact (eq_refl (term990 A B t R x y)). Qed.
Lemma lem6999576 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1043 A B t R x y) = (term994 A B t R x y).
Proof. exact (MK_COMB (@lem6999575 A B t R x y) (@lem6999574 A B t R x y)). Qed.
Lemma lem6999577 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6999578 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1048 A B t R x y) = (term1049 A B t R x y).
Proof. exact (MK_COMB (@lem6999577) (@lem6999576 A B t R x y)). Qed.
Lemma lem6999579 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term1045 A B t R x y y') = (term991 A B t R x y' y).
Proof. exact (eq_refl (term1045 A B t R x y y')). Qed.
Lemma lem6999580 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term990 A B t R x y) = (term990 A B t R x y).
Proof. exact (eq_refl (term990 A B t R x y)). Qed.
Lemma lem6999581 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term1050 A B t R x y y') = (term1051 A B t R x y' y).
Proof. exact (MK_COMB (@lem6999580 A B t R x y) (@lem6999579 A B t R x y' y)). Qed.
Lemma lem6999582 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1052 A B t R x y) = (term1053 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem6999581 A B t R x y' y)). Qed.
Lemma lem6999583 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6999584 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1044 A B t R x y) = (term1054 A B t R x y).
Proof. exact (MK_COMB (@lem6999583 B) (@lem6999582 A B t R x y)). Qed.
Lemma lem6999585 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : ((term1043 A B t R x y) = (term1044 A B t R x y)) = ((term994 A B t R x y) = (term1054 A B t R x y)).
Proof. exact (MK_COMB (@lem6999578 A B t R x y) (@lem6999584 A B t R x y)). Qed.
Lemma lem6999586 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term994 A B t R x y) = (term1054 A B t R x y).
Proof. exact (EQ_MP (@lem6999585 A B t R x y) (@lem6999570 A B t R x y)). Qed.
Lemma lem6999587 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term995 A B t R x) = (term1055 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem6999586 A B t R x y)). Qed.
Lemma lem6999588 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6999589 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term996 A B t R x) = (term1056 A B t R x).
Proof. exact (MK_COMB (@lem6999588 B) (@lem6999587 A B t R x)). Qed.
Lemma lem6999590 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1005 A B t R y x) = (term1005 A B t R y x).
Proof. exact (eq_refl (term1005 A B t R y x)). Qed.
Lemma lem6999591 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1007 A B y t R x) = (term1057 A B y t R x).
Proof. exact (MK_COMB (@lem6999590 A B t R y x) (@lem6999589 A B t R x)). Qed.
Lemma lem6999593 {A : Type'} (P : Prop) (Q : A -> Prop) : (term469 A P Q) = (term470 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem6999594 {B : Type'} (P : Prop) (Q : B -> Prop) : (term469 B P Q) = (term470 B P Q).
Proof. exact (@lem6999593 B P Q). Qed.
Lemma lem6999595 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1058 A B y t R x) = (term1059 A B y t R x).
Proof. exact (@lem6999594 B (term1003 A B t R y x) (term1055 A B t R x)). Qed.
Lemma lem6999596 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1060 A B t R x y) = (term1054 A B t R x y).
Proof. exact (eq_refl (term1060 A B t R x y)). Qed.
Lemma lem6999597 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term1061 A B t R x) = (term1055 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem6999596 A B t R x y)). Qed.
Lemma lem6999598 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6999599 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term1062 A B t R x) = (term1056 A B t R x).
Proof. exact (MK_COMB (@lem6999598 B) (@lem6999597 A B t R x)). Qed.
Lemma lem6999600 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1005 A B t R y x) = (term1005 A B t R y x).
Proof. exact (eq_refl (term1005 A B t R y x)). Qed.
Lemma lem6999601 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1058 A B y t R x) = (term1057 A B y t R x).
Proof. exact (MK_COMB (@lem6999600 A B t R y x) (@lem6999599 A B t R x)). Qed.
Lemma lem6999602 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6999603 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1063 A B y t R x) = (term1064 A B y t R x).
Proof. exact (MK_COMB (@lem6999602) (@lem6999601 A B y t R x)). Qed.
Lemma lem6999604 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1060 A B t R x y) = (term1054 A B t R x y).
Proof. exact (eq_refl (term1060 A B t R x y)). Qed.
Lemma lem6999605 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1005 A B t R y x) = (term1005 A B t R y x).
Proof. exact (eq_refl (term1005 A B t R y x)). Qed.
Lemma lem6999606 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1065 A B y t R x y') = (term1066 A B y t R x y').
Proof. exact (MK_COMB (@lem6999605 A B t R y x) (@lem6999604 A B t R x y')). Qed.
Lemma lem6999607 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1067 A B y t R x) = (term1068 A B y t R x).
Proof. exact (fun_ext (fun y' : B => @lem6999606 A B y t R x y')). Qed.
Lemma lem6999608 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6999609 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1059 A B y t R x) = (term1069 A B y t R x).
Proof. exact (MK_COMB (@lem6999608 B) (@lem6999607 A B y t R x)). Qed.
Lemma lem6999610 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : ((term1058 A B y t R x) = (term1059 A B y t R x)) = ((term1057 A B y t R x) = (term1069 A B y t R x)).
Proof. exact (MK_COMB (@lem6999603 A B y t R x) (@lem6999609 A B y t R x)). Qed.
Lemma lem6999611 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1057 A B y t R x) = (term1069 A B y t R x).
Proof. exact (EQ_MP (@lem6999610 A B y t R x) (@lem6999595 A B y t R x)). Qed.
Lemma lem6999613 {A : Type'} (P : Prop) (Q : A -> Prop) : (term469 A P Q) = (term470 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem6999614 {B : Type'} (P : Prop) (Q : B -> Prop) : (term469 B P Q) = (term470 B P Q).
Proof. exact (@lem6999613 B P Q). Qed.
Lemma lem6999615 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1070 A B y t R x y') = (term1071 A B y t R x y').
Proof. exact (@lem6999614 B (term1003 A B t R y x) (term1053 A B t R x y')). Qed.
Lemma lem6999616 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term1072 A B t R x y y') = (term1051 A B t R x y' y).
Proof. exact (eq_refl (term1072 A B t R x y y')). Qed.
Lemma lem6999617 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1073 A B t R x y) = (term1053 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem6999616 A B t R x y' y)). Qed.
Lemma lem6999618 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6999619 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1074 A B t R x y) = (term1054 A B t R x y).
Proof. exact (MK_COMB (@lem6999618 B) (@lem6999617 A B t R x y)). Qed.
Lemma lem6999620 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1005 A B t R y x) = (term1005 A B t R y x).
Proof. exact (eq_refl (term1005 A B t R y x)). Qed.
Lemma lem6999621 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1070 A B y t R x y') = (term1066 A B y t R x y').
Proof. exact (MK_COMB (@lem6999620 A B t R y x) (@lem6999619 A B t R x y')). Qed.
Lemma lem6999622 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6999623 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1075 A B y t R x y') = (term1076 A B y t R x y').
Proof. exact (MK_COMB (@lem6999622) (@lem6999621 A B y t R x y')). Qed.
Lemma lem6999624 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term1072 A B t R x y y') = (term1051 A B t R x y' y).
Proof. exact (eq_refl (term1072 A B t R x y y')). Qed.
Lemma lem6999625 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1005 A B t R y x) = (term1005 A B t R y x).
Proof. exact (eq_refl (term1005 A B t R y x)). Qed.
Lemma lem6999626 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term1077 A B y t R x y'' y') = (term1078 A B y t R x y' y'').
Proof. exact (MK_COMB (@lem6999625 A B t R y x) (@lem6999624 A B t R x y' y'')). Qed.
Lemma lem6999627 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1079 A B y t R x y') = (term1080 A B y t R x y').
Proof. exact (fun_ext (fun y'' : B => @lem6999626 A B y t R x y'' y')). Qed.
Lemma lem6999628 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6999629 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1071 A B y t R x y') = (term1081 A B y t R x y').
Proof. exact (MK_COMB (@lem6999628 B) (@lem6999627 A B y t R x y')). Qed.
Lemma lem6999630 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : ((term1070 A B y t R x y') = (term1071 A B y t R x y')) = ((term1066 A B y t R x y') = (term1081 A B y t R x y')).
Proof. exact (MK_COMB (@lem6999623 A B y t R x y') (@lem6999629 A B y t R x y')). Qed.
Lemma lem6999631 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1066 A B y t R x y') = (term1081 A B y t R x y').
Proof. exact (EQ_MP (@lem6999630 A B y t R x y') (@lem6999615 A B y t R x y')). Qed.
Lemma lem6999632 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1068 A B y t R x) = (term1082 A B y t R x).
Proof. exact (fun_ext (fun y' : B => @lem6999631 A B y t R x y')). Qed.
Lemma lem6999633 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6999634 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1069 A B y t R x) = (term1083 A B y t R x).
Proof. exact (MK_COMB (@lem6999633 B) (@lem6999632 A B y t R x)). Qed.
Lemma lem6999635 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1057 A B y t R x) = (term1083 A B y t R x).
Proof. exact (TRANS (@lem6999611 A B y t R x) (@lem6999634 A B y t R x)). Qed.
Lemma lem6999636 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1007 A B y t R x) = (term1083 A B y t R x).
Proof. exact (TRANS (@lem6999591 A B y t R x) (@lem6999635 A B y t R x)). Qed.
Lemma lem6999637 {A : Type'} (s : A -> Prop) (x : A) : (term964 A s x) = (term964 A s x).
Proof. exact (eq_refl (term964 A s x)). Qed.
Lemma lem6999638 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1008 A B s y t R x) = (term1084 A B s y t R x).
Proof. exact (MK_COMB (@lem6999637 A s x) (@lem6999636 A B y t R x)). Qed.
Lemma lem6999640 {A : Type'} (P : Prop) (Q : A -> Prop) : (term292 A P Q) = (term291 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem6999641 {B : Type'} (P : Prop) (Q : B -> Prop) : (term292 B P Q) = (term291 B P Q).
Proof. exact (@lem6999640 B P Q). Qed.
Lemma lem6999642 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1085 A B s y t R x) = (term1086 A B s y t R x).
Proof. exact (@lem6999641 B (term963 A s x) (term1082 A B y t R x)). Qed.
Lemma lem6999643 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1087 A B y t R x y') = (term1081 A B y t R x y').
Proof. exact (eq_refl (term1087 A B y t R x y')). Qed.
Lemma lem6999644 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1088 A B y t R x) = (term1082 A B y t R x).
Proof. exact (fun_ext (fun y' : B => @lem6999643 A B y t R x y')). Qed.
Lemma lem6999645 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6999646 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1089 A B y t R x) = (term1083 A B y t R x).
Proof. exact (MK_COMB (@lem6999645 B) (@lem6999644 A B y t R x)). Qed.
Lemma lem6999647 {A : Type'} (s : A -> Prop) (x : A) : (term964 A s x) = (term964 A s x).
Proof. exact (eq_refl (term964 A s x)). Qed.
Lemma lem6999648 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1085 A B s y t R x) = (term1084 A B s y t R x).
Proof. exact (MK_COMB (@lem6999647 A s x) (@lem6999646 A B y t R x)). Qed.
Lemma lem6999649 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6999650 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1090 A B s y t R x) = (term1091 A B s y t R x).
Proof. exact (MK_COMB (@lem6999649) (@lem6999648 A B s y t R x)). Qed.
Lemma lem6999651 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1087 A B y t R x y') = (term1081 A B y t R x y').
Proof. exact (eq_refl (term1087 A B y t R x y')). Qed.
Lemma lem6999652 {A : Type'} (s : A -> Prop) (x : A) : (term964 A s x) = (term964 A s x).
Proof. exact (eq_refl (term964 A s x)). Qed.
Lemma lem6999653 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1092 A B s y t R x y') = (term1093 A B s y t R x y').
Proof. exact (MK_COMB (@lem6999652 A s x) (@lem6999651 A B y t R x y')). Qed.
Lemma lem6999654 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1094 A B s y t R x) = (term1095 A B s y t R x).
Proof. exact (fun_ext (fun y' : B => @lem6999653 A B s y t R x y')). Qed.
Lemma lem6999655 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6999656 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1086 A B s y t R x) = (term1096 A B s y t R x).
Proof. exact (MK_COMB (@lem6999655 B) (@lem6999654 A B s y t R x)). Qed.
Lemma lem6999657 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : ((term1085 A B s y t R x) = (term1086 A B s y t R x)) = ((term1084 A B s y t R x) = (term1096 A B s y t R x)).
Proof. exact (MK_COMB (@lem6999650 A B s y t R x) (@lem6999656 A B s y t R x)). Qed.
Lemma lem6999658 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1084 A B s y t R x) = (term1096 A B s y t R x).
Proof. exact (EQ_MP (@lem6999657 A B s y t R x) (@lem6999642 A B s y t R x)). Qed.
Lemma lem6999660 {A : Type'} (P : Prop) (Q : A -> Prop) : (term292 A P Q) = (term291 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem6999661 {B : Type'} (P : Prop) (Q : B -> Prop) : (term292 B P Q) = (term291 B P Q).
Proof. exact (@lem6999660 B P Q). Qed.
Lemma lem6999662 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1097 A B s y t R x y') = (term1098 A B s y t R x y').
Proof. exact (@lem6999661 B (term963 A s x) (term1080 A B y t R x y')). Qed.
Lemma lem6999663 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term1099 A B y t R x y'' y') = (term1078 A B y t R x y' y'').
Proof. exact (eq_refl (term1099 A B y t R x y'' y')). Qed.
Lemma lem6999664 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1100 A B y t R x y') = (term1080 A B y t R x y').
Proof. exact (fun_ext (fun y'' : B => @lem6999663 A B y t R x y'' y')). Qed.
Lemma lem6999665 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6999666 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1101 A B y t R x y') = (term1081 A B y t R x y').
Proof. exact (MK_COMB (@lem6999665 B) (@lem6999664 A B y t R x y')). Qed.
Lemma lem6999667 {A : Type'} (s : A -> Prop) (x : A) : (term964 A s x) = (term964 A s x).
Proof. exact (eq_refl (term964 A s x)). Qed.
Lemma lem6999668 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1097 A B s y t R x y') = (term1093 A B s y t R x y').
Proof. exact (MK_COMB (@lem6999667 A s x) (@lem6999666 A B y t R x y')). Qed.
Lemma lem6999669 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6999670 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1102 A B s y t R x y') = (term1103 A B s y t R x y').
Proof. exact (MK_COMB (@lem6999669) (@lem6999668 A B s y t R x y')). Qed.
Lemma lem6999671 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term1099 A B y t R x y'' y') = (term1078 A B y t R x y' y'').
Proof. exact (eq_refl (term1099 A B y t R x y'' y')). Qed.
Lemma lem6999672 {A : Type'} (s : A -> Prop) (x : A) : (term964 A s x) = (term964 A s x).
Proof. exact (eq_refl (term964 A s x)). Qed.
Lemma lem6999673 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term1104 A B s y t R x y'' y') = (term1105 A B s y t R x y' y'').
Proof. exact (MK_COMB (@lem6999672 A s x) (@lem6999671 A B y t R x y' y'')). Qed.
Lemma lem6999674 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1106 A B s y t R x y') = (term1107 A B s y t R x y').
Proof. exact (fun_ext (fun y'' : B => @lem6999673 A B s y t R x y'' y')). Qed.
Lemma lem6999675 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6999676 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1098 A B s y t R x y') = (term1108 A B s y t R x y').
Proof. exact (MK_COMB (@lem6999675 B) (@lem6999674 A B s y t R x y')). Qed.
Lemma lem6999677 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : ((term1097 A B s y t R x y') = (term1098 A B s y t R x y')) = ((term1093 A B s y t R x y') = (term1108 A B s y t R x y')).
Proof. exact (MK_COMB (@lem6999670 A B s y t R x y') (@lem6999676 A B s y t R x y')). Qed.
Lemma lem6999678 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1093 A B s y t R x y') = (term1108 A B s y t R x y').
Proof. exact (EQ_MP (@lem6999677 A B s y t R x y') (@lem6999662 A B s y t R x y')). Qed.
Lemma lem6999679 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1095 A B s y t R x) = (term1109 A B s y t R x).
Proof. exact (fun_ext (fun y' : B => @lem6999678 A B s y t R x y')). Qed.
Lemma lem6999680 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6999681 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1096 A B s y t R x) = (term1110 A B s y t R x).
Proof. exact (MK_COMB (@lem6999680 B) (@lem6999679 A B s y t R x)). Qed.
Lemma lem6999682 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1084 A B s y t R x) = (term1110 A B s y t R x).
Proof. exact (TRANS (@lem6999658 A B s y t R x) (@lem6999681 A B s y t R x)). Qed.
Lemma lem6999683 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1008 A B s y t R x) = (term1110 A B s y t R x).
Proof. exact (TRANS (@lem6999638 A B s y t R x) (@lem6999682 A B s y t R x)). Qed.
Lemma lem6999684 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term1009 A B s y t R) = (term1111 A B s y t R).
Proof. exact (fun_ext (fun x : A => @lem6999683 A B s y t R x)). Qed.
Lemma lem6999685 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6999686 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term1010 A B s y t R) = (term1112 A B s y t R).
Proof. exact (MK_COMB (@lem6999685 A) (@lem6999684 A B s y t R)). Qed.
Lemma lem6999724 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term1105 A B s y t R x y' y'') = (term1113 A B y s t R x y' y'').
Proof. exact (@lem19490 (term1003 A B t R y x) (term963 A s x) (term1051 A B t R x y' y'')). Qed.
Lemma lem6999725 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term1114 A B s t R x y' y) = (term1114 A B s t R x y' y).
Proof. exact (eq_refl (term1114 A B s t R x y' y)). Qed.
Lemma lem6999732 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1115 A B s t R y x) = (term1116 A B t s R y x).
Proof. exact (@lem19490 (term999 A B t y x) (term963 A s x) (term406 A B R y x)). Qed.
Lemma lem6999733 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6999734 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1117 A B s t R y x) = (term1118 A B t s R y x).
Proof. exact (MK_COMB (@lem6999733) (@lem6999732 A B t s R y x)). Qed.
Lemma lem6999735 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term1113 A B y s t R x y' y'') = (term1119 A B y s t R x y' y'').
Proof. exact (MK_COMB (@lem6999734 A B t s R y x) (@lem6999725 A B s t R x y' y'')). Qed.
Lemma lem6999737 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term1105 A B s y t R x y' y'') = (term1119 A B y s t R x y' y'').
Proof. exact (TRANS (@lem6999724 A B y s t R x y' y'') (@lem6999735 A B y s t R x y' y'')). Qed.
Lemma lem6999738 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1107 A B s y t R x y') = (term1120 A B y s t R x y').
Proof. exact (fun_ext (fun y'' : B => @lem6999737 A B y s t R x y'' y')). Qed.
Lemma lem6999739 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6999740 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1108 A B s y t R x y') = (term1121 A B y s t R x y').
Proof. exact (MK_COMB (@lem6999739 B) (@lem6999738 A B y s t R x y')). Qed.
Lemma lem6999741 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1109 A B s y t R x) = (term1122 A B y s t R x).
Proof. exact (fun_ext (fun y' : B => @lem6999740 A B y s t R x y')). Qed.
Lemma lem6999742 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6999743 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1110 A B s y t R x) = (term1123 A B y s t R x).
Proof. exact (MK_COMB (@lem6999742 B) (@lem6999741 A B y s t R x)). Qed.
Lemma lem6999744 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term1111 A B s y t R) = (term1124 A B y s t R).
Proof. exact (fun_ext (fun x : A => @lem6999743 A B y s t R x)). Qed.
Lemma lem6999745 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6999746 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term1112 A B s y t R) = (term1125 A B y s t R).
Proof. exact (MK_COMB (@lem6999745 A) (@lem6999744 A B y s t R)). Qed.
Lemma lem6999747 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term1010 A B s y t R) = (term1125 A B y s t R).
Proof. exact (TRANS (@lem6999686 A B s y t R) (@lem6999746 A B y s t R)). Qed.
Lemma lem6999748 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1125 A B y s t R.
Proof. exact (EQ_MP (@lem6999747 A B y s t R) (@lem6999206 A B x y t R s h1)). Qed.
Lemma lem6999764 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term983 A B _93304 t R x' x) : term983 A B _93304 t R x' x.
Proof. exact (h1). Qed.
Lemma lem7000036 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term963 A s x') : term963 A s x'.
Proof. exact (h1). Qed.
Lemma lem7000038 {A : Type'} (P : A -> Prop) (Q : Prop) : (term242 A P Q) = (term241 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem7000039 {B : Type'} (P : B -> Prop) (Q : Prop) : (term242 B P Q) = (term241 B P Q).
Proof. exact (@lem7000038 B P Q). Qed.
Lemma lem7000040 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1014 A B _93304 t R x) = (term1015 A B _93304 t R x).
Proof. exact (@lem7000039 B (term966 A B t R x) (term962 A B _93304 t R x)). Qed.
Lemma lem7000041 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term1016 A B t R x x') = (term965 A B t R x x').
Proof. exact (eq_refl (term1016 A B t R x x')). Qed.
Lemma lem7000042 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term1017 A B t R x) = (term966 A B t R x).
Proof. exact (fun_ext (fun x' : B => @lem7000041 A B t R x x')). Qed.
Lemma lem7000043 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7000044 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term1018 A B t R x) = (term967 A B t R x).
Proof. exact (MK_COMB (@lem7000043 B) (@lem7000042 A B t R x)). Qed.
Lemma lem7000045 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7000046 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term1019 A B t R x) = (term968 A B t R x).
Proof. exact (MK_COMB (@lem7000045) (@lem7000044 A B t R x)). Qed.
Lemma lem7000047 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term962 A B _93304 t R x) = (term962 A B _93304 t R x).
Proof. exact (eq_refl (term962 A B _93304 t R x)). Qed.
Lemma lem7000048 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1014 A B _93304 t R x) = (term969 A B _93304 t R x).
Proof. exact (MK_COMB (@lem7000046 A B t R x) (@lem7000047 A B _93304 t R x)). Qed.
Lemma lem7000049 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7000050 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1020 A B _93304 t R x) = (term1021 A B _93304 t R x).
Proof. exact (MK_COMB (@lem7000049) (@lem7000048 A B _93304 t R x)). Qed.
Lemma lem7000051 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term1016 A B t R x x') = (term965 A B t R x x').
Proof. exact (eq_refl (term1016 A B t R x x')). Qed.
Lemma lem7000052 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7000053 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (x' : B) : (term1022 A B t R x x') = (term990 A B t R x x').
Proof. exact (MK_COMB (@lem7000052) (@lem7000051 A B t R x x')). Qed.
Lemma lem7000054 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term962 A B _93304 t R x) = (term962 A B _93304 t R x).
Proof. exact (eq_refl (term962 A B _93304 t R x)). Qed.
Lemma lem7000055 {A B : Type'} (x : B) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term1023 A B x _93304 t R x') = (term1024 A B x _93304 t R x').
Proof. exact (MK_COMB (@lem7000053 A B t R x' x) (@lem7000054 A B _93304 t R x')). Qed.
Lemma lem7000056 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1025 A B _93304 t R x) = (term1026 A B _93304 t R x).
Proof. exact (fun_ext (fun x' : B => @lem7000055 A B x' _93304 t R x)). Qed.
Lemma lem7000057 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7000058 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1015 A B _93304 t R x) = (term1027 A B _93304 t R x).
Proof. exact (MK_COMB (@lem7000057 B) (@lem7000056 A B _93304 t R x)). Qed.
Lemma lem7000059 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : ((term1014 A B _93304 t R x) = (term1015 A B _93304 t R x)) = ((term969 A B _93304 t R x) = (term1027 A B _93304 t R x)).
Proof. exact (MK_COMB (@lem7000050 A B _93304 t R x) (@lem7000058 A B _93304 t R x)). Qed.
Lemma lem7000060 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term969 A B _93304 t R x) = (term1027 A B _93304 t R x).
Proof. exact (EQ_MP (@lem7000059 A B _93304 t R x) (@lem7000040 A B _93304 t R x)). Qed.
Lemma lem7000061 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term970 A B _93304 t R) = (term1028 A B _93304 t R).
Proof. exact (fun_ext (fun x : A => @lem7000060 A B _93304 t R x)). Qed.
Lemma lem7000062 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7000063 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term971 A B _93304 t R) = (term1029 A B _93304 t R).
Proof. exact (MK_COMB (@lem7000062 A) (@lem7000061 A B _93304 t R)). Qed.
Lemma lem7000064 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) : (term972 A B _93304 t) = (term1030 A B _93304 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem7000063 A B _93304 t R)). Qed.
Lemma lem7000065 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem7000066 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) : (term973 A B _93304 t) = (term1031 A B _93304 t).
Proof. exact (MK_COMB (@lem7000065 A B) (@lem7000064 A B _93304 t)). Qed.
Lemma lem7000067 {A B : Type'} (_93304 : type830 A B) : (term974 A B _93304) = (term1032 A B _93304).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7000066 A B _93304 t)). Qed.
Lemma lem7000068 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7000069 {A B : Type'} (_93304 : type830 A B) : (term975 A B _93304) = (term1033 A B _93304).
Proof. exact (MK_COMB (@lem7000068 B) (@lem7000067 A B _93304)). Qed.
Lemma lem7000092 {A B : Type'} (x : B) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term1024 A B x _93304 t R x') = (term1034 A B x _93304 t R x').
Proof. exact (@lem19490 (term960 A B _93304 t R x') (term965 A B t R x' x) (term370 A B _93304 t R x')). Qed.
Lemma lem7000093 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1026 A B _93304 t R x) = (term1035 A B _93304 t R x).
Proof. exact (fun_ext (fun x' : B => @lem7000092 A B x' _93304 t R x)). Qed.
Lemma lem7000094 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7000095 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1027 A B _93304 t R x) = (term1036 A B _93304 t R x).
Proof. exact (MK_COMB (@lem7000094 B) (@lem7000093 A B _93304 t R x)). Qed.
Lemma lem7000096 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term1028 A B _93304 t R) = (term1037 A B _93304 t R).
Proof. exact (fun_ext (fun x : A => @lem7000095 A B _93304 t R x)). Qed.
Lemma lem7000097 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7000098 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) : (term1029 A B _93304 t R) = (term1038 A B _93304 t R).
Proof. exact (MK_COMB (@lem7000097 A) (@lem7000096 A B _93304 t R)). Qed.
Lemma lem7000099 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) : (term1030 A B _93304 t) = (term1039 A B _93304 t).
Proof. exact (fun_ext (fun R : type1413 A B => @lem7000098 A B _93304 t R)). Qed.
Lemma lem7000100 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem7000101 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) : (term1031 A B _93304 t) = (term1040 A B _93304 t).
Proof. exact (MK_COMB (@lem7000100 A B) (@lem7000099 A B _93304 t)). Qed.
Lemma lem7000102 {A B : Type'} (_93304 : type830 A B) : (term1032 A B _93304) = (term1041 A B _93304).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7000101 A B _93304 t)). Qed.
Lemma lem7000103 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7000104 {A B : Type'} (_93304 : type830 A B) : (term1033 A B _93304) = (term1042 A B _93304).
Proof. exact (MK_COMB (@lem7000103 B) (@lem7000102 A B _93304)). Qed.
Lemma lem7000105 {A B : Type'} (_93304 : type830 A B) : (term975 A B _93304) = (term1042 A B _93304).
Proof. exact (TRANS (@lem7000069 A B _93304) (@lem7000104 A B _93304)). Qed.
Lemma lem7000106 {A B : Type'} (_93304 : type830 A B) (h1 : term728 A B _93304) : term1042 A B _93304.
Proof. exact (EQ_MP (@lem7000105 A B _93304) (@lem6998881 A B _93304 h1)). Qed.
Lemma lem7000112 {A : Type'} (P : Prop) (Q : A -> Prop) : (term292 A P Q) = (term291 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7000113 {B : Type'} (P : Prop) (Q : B -> Prop) : (term292 B P Q) = (term291 B P Q).
Proof. exact (@lem7000112 B P Q). Qed.
Lemma lem7000114 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1043 A B t R x y) = (term1044 A B t R x y).
Proof. exact (@lem7000113 B (term965 A B t R x y) (term992 A B t R x y)). Qed.
Lemma lem7000115 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term1045 A B t R x y y') = (term991 A B t R x y' y).
Proof. exact (eq_refl (term1045 A B t R x y y')). Qed.
Lemma lem7000116 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1046 A B t R x y) = (term992 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem7000115 A B t R x y' y)). Qed.
Lemma lem7000117 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7000118 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1047 A B t R x y) = (term993 A B t R x y).
Proof. exact (MK_COMB (@lem7000117 B) (@lem7000116 A B t R x y)). Qed.
Lemma lem7000119 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term990 A B t R x y) = (term990 A B t R x y).
Proof. exact (eq_refl (term990 A B t R x y)). Qed.
Lemma lem7000120 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1043 A B t R x y) = (term994 A B t R x y).
Proof. exact (MK_COMB (@lem7000119 A B t R x y) (@lem7000118 A B t R x y)). Qed.
Lemma lem7000121 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7000122 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1048 A B t R x y) = (term1049 A B t R x y).
Proof. exact (MK_COMB (@lem7000121) (@lem7000120 A B t R x y)). Qed.
Lemma lem7000123 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term1045 A B t R x y y') = (term991 A B t R x y' y).
Proof. exact (eq_refl (term1045 A B t R x y y')). Qed.
Lemma lem7000124 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term990 A B t R x y) = (term990 A B t R x y).
Proof. exact (eq_refl (term990 A B t R x y)). Qed.
Lemma lem7000125 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term1050 A B t R x y y') = (term1051 A B t R x y' y).
Proof. exact (MK_COMB (@lem7000124 A B t R x y) (@lem7000123 A B t R x y' y)). Qed.
Lemma lem7000126 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1052 A B t R x y) = (term1053 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem7000125 A B t R x y' y)). Qed.
Lemma lem7000127 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7000128 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1044 A B t R x y) = (term1054 A B t R x y).
Proof. exact (MK_COMB (@lem7000127 B) (@lem7000126 A B t R x y)). Qed.
Lemma lem7000129 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : ((term1043 A B t R x y) = (term1044 A B t R x y)) = ((term994 A B t R x y) = (term1054 A B t R x y)).
Proof. exact (MK_COMB (@lem7000122 A B t R x y) (@lem7000128 A B t R x y)). Qed.
Lemma lem7000130 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term994 A B t R x y) = (term1054 A B t R x y).
Proof. exact (EQ_MP (@lem7000129 A B t R x y) (@lem7000114 A B t R x y)). Qed.
Lemma lem7000131 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term995 A B t R x) = (term1055 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem7000130 A B t R x y)). Qed.
Lemma lem7000132 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7000133 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term996 A B t R x) = (term1056 A B t R x).
Proof. exact (MK_COMB (@lem7000132 B) (@lem7000131 A B t R x)). Qed.
Lemma lem7000134 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1005 A B t R y x) = (term1005 A B t R y x).
Proof. exact (eq_refl (term1005 A B t R y x)). Qed.
Lemma lem7000135 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1007 A B y t R x) = (term1057 A B y t R x).
Proof. exact (MK_COMB (@lem7000134 A B t R y x) (@lem7000133 A B t R x)). Qed.
Lemma lem7000137 {A : Type'} (P : Prop) (Q : A -> Prop) : (term469 A P Q) = (term470 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem7000138 {B : Type'} (P : Prop) (Q : B -> Prop) : (term469 B P Q) = (term470 B P Q).
Proof. exact (@lem7000137 B P Q). Qed.
Lemma lem7000139 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1058 A B y t R x) = (term1059 A B y t R x).
Proof. exact (@lem7000138 B (term1003 A B t R y x) (term1055 A B t R x)). Qed.
Lemma lem7000140 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1060 A B t R x y) = (term1054 A B t R x y).
Proof. exact (eq_refl (term1060 A B t R x y)). Qed.
Lemma lem7000141 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term1061 A B t R x) = (term1055 A B t R x).
Proof. exact (fun_ext (fun y : B => @lem7000140 A B t R x y)). Qed.
Lemma lem7000142 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7000143 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term1062 A B t R x) = (term1056 A B t R x).
Proof. exact (MK_COMB (@lem7000142 B) (@lem7000141 A B t R x)). Qed.
Lemma lem7000144 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1005 A B t R y x) = (term1005 A B t R y x).
Proof. exact (eq_refl (term1005 A B t R y x)). Qed.
Lemma lem7000145 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1058 A B y t R x) = (term1057 A B y t R x).
Proof. exact (MK_COMB (@lem7000144 A B t R y x) (@lem7000143 A B t R x)). Qed.
Lemma lem7000146 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7000147 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1063 A B y t R x) = (term1064 A B y t R x).
Proof. exact (MK_COMB (@lem7000146) (@lem7000145 A B y t R x)). Qed.
Lemma lem7000148 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1060 A B t R x y) = (term1054 A B t R x y).
Proof. exact (eq_refl (term1060 A B t R x y)). Qed.
Lemma lem7000149 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1005 A B t R y x) = (term1005 A B t R y x).
Proof. exact (eq_refl (term1005 A B t R y x)). Qed.
Lemma lem7000150 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1065 A B y t R x y') = (term1066 A B y t R x y').
Proof. exact (MK_COMB (@lem7000149 A B t R y x) (@lem7000148 A B t R x y')). Qed.
Lemma lem7000151 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1067 A B y t R x) = (term1068 A B y t R x).
Proof. exact (fun_ext (fun y' : B => @lem7000150 A B y t R x y')). Qed.
Lemma lem7000152 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7000153 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1059 A B y t R x) = (term1069 A B y t R x).
Proof. exact (MK_COMB (@lem7000152 B) (@lem7000151 A B y t R x)). Qed.
Lemma lem7000154 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : ((term1058 A B y t R x) = (term1059 A B y t R x)) = ((term1057 A B y t R x) = (term1069 A B y t R x)).
Proof. exact (MK_COMB (@lem7000147 A B y t R x) (@lem7000153 A B y t R x)). Qed.
Lemma lem7000155 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1057 A B y t R x) = (term1069 A B y t R x).
Proof. exact (EQ_MP (@lem7000154 A B y t R x) (@lem7000139 A B y t R x)). Qed.
Lemma lem7000157 {A : Type'} (P : Prop) (Q : A -> Prop) : (term469 A P Q) = (term470 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem7000158 {B : Type'} (P : Prop) (Q : B -> Prop) : (term469 B P Q) = (term470 B P Q).
Proof. exact (@lem7000157 B P Q). Qed.
Lemma lem7000159 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1070 A B y t R x y') = (term1071 A B y t R x y').
Proof. exact (@lem7000158 B (term1003 A B t R y x) (term1053 A B t R x y')). Qed.
Lemma lem7000160 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term1072 A B t R x y y') = (term1051 A B t R x y' y).
Proof. exact (eq_refl (term1072 A B t R x y y')). Qed.
Lemma lem7000161 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1073 A B t R x y) = (term1053 A B t R x y).
Proof. exact (fun_ext (fun y' : B => @lem7000160 A B t R x y' y)). Qed.
Lemma lem7000162 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7000163 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y : B) : (term1074 A B t R x y) = (term1054 A B t R x y).
Proof. exact (MK_COMB (@lem7000162 B) (@lem7000161 A B t R x y)). Qed.
Lemma lem7000164 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1005 A B t R y x) = (term1005 A B t R y x).
Proof. exact (eq_refl (term1005 A B t R y x)). Qed.
Lemma lem7000165 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1070 A B y t R x y') = (term1066 A B y t R x y').
Proof. exact (MK_COMB (@lem7000164 A B t R y x) (@lem7000163 A B t R x y')). Qed.
Lemma lem7000166 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7000167 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1075 A B y t R x y') = (term1076 A B y t R x y').
Proof. exact (MK_COMB (@lem7000166) (@lem7000165 A B y t R x y')). Qed.
Lemma lem7000168 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term1072 A B t R x y y') = (term1051 A B t R x y' y).
Proof. exact (eq_refl (term1072 A B t R x y y')). Qed.
Lemma lem7000169 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1005 A B t R y x) = (term1005 A B t R y x).
Proof. exact (eq_refl (term1005 A B t R y x)). Qed.
Lemma lem7000170 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term1077 A B y t R x y'' y') = (term1078 A B y t R x y' y'').
Proof. exact (MK_COMB (@lem7000169 A B t R y x) (@lem7000168 A B t R x y' y'')). Qed.
Lemma lem7000171 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1079 A B y t R x y') = (term1080 A B y t R x y').
Proof. exact (fun_ext (fun y'' : B => @lem7000170 A B y t R x y'' y')). Qed.
Lemma lem7000172 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7000173 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1071 A B y t R x y') = (term1081 A B y t R x y').
Proof. exact (MK_COMB (@lem7000172 B) (@lem7000171 A B y t R x y')). Qed.
Lemma lem7000174 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : ((term1070 A B y t R x y') = (term1071 A B y t R x y')) = ((term1066 A B y t R x y') = (term1081 A B y t R x y')).
Proof. exact (MK_COMB (@lem7000167 A B y t R x y') (@lem7000173 A B y t R x y')). Qed.
Lemma lem7000175 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1066 A B y t R x y') = (term1081 A B y t R x y').
Proof. exact (EQ_MP (@lem7000174 A B y t R x y') (@lem7000159 A B y t R x y')). Qed.
Lemma lem7000176 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1068 A B y t R x) = (term1082 A B y t R x).
Proof. exact (fun_ext (fun y' : B => @lem7000175 A B y t R x y')). Qed.
Lemma lem7000177 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7000178 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1069 A B y t R x) = (term1083 A B y t R x).
Proof. exact (MK_COMB (@lem7000177 B) (@lem7000176 A B y t R x)). Qed.
Lemma lem7000179 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1057 A B y t R x) = (term1083 A B y t R x).
Proof. exact (TRANS (@lem7000155 A B y t R x) (@lem7000178 A B y t R x)). Qed.
Lemma lem7000180 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1007 A B y t R x) = (term1083 A B y t R x).
Proof. exact (TRANS (@lem7000135 A B y t R x) (@lem7000179 A B y t R x)). Qed.
Lemma lem7000181 {A : Type'} (s : A -> Prop) (x : A) : (term964 A s x) = (term964 A s x).
Proof. exact (eq_refl (term964 A s x)). Qed.
Lemma lem7000182 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1008 A B s y t R x) = (term1084 A B s y t R x).
Proof. exact (MK_COMB (@lem7000181 A s x) (@lem7000180 A B y t R x)). Qed.
Lemma lem7000184 {A : Type'} (P : Prop) (Q : A -> Prop) : (term292 A P Q) = (term291 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7000185 {B : Type'} (P : Prop) (Q : B -> Prop) : (term292 B P Q) = (term291 B P Q).
Proof. exact (@lem7000184 B P Q). Qed.
Lemma lem7000186 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1085 A B s y t R x) = (term1086 A B s y t R x).
Proof. exact (@lem7000185 B (term963 A s x) (term1082 A B y t R x)). Qed.
Lemma lem7000187 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1087 A B y t R x y') = (term1081 A B y t R x y').
Proof. exact (eq_refl (term1087 A B y t R x y')). Qed.
Lemma lem7000188 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1088 A B y t R x) = (term1082 A B y t R x).
Proof. exact (fun_ext (fun y' : B => @lem7000187 A B y t R x y')). Qed.
Lemma lem7000189 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7000190 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1089 A B y t R x) = (term1083 A B y t R x).
Proof. exact (MK_COMB (@lem7000189 B) (@lem7000188 A B y t R x)). Qed.
Lemma lem7000191 {A : Type'} (s : A -> Prop) (x : A) : (term964 A s x) = (term964 A s x).
Proof. exact (eq_refl (term964 A s x)). Qed.
Lemma lem7000192 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1085 A B s y t R x) = (term1084 A B s y t R x).
Proof. exact (MK_COMB (@lem7000191 A s x) (@lem7000190 A B y t R x)). Qed.
Lemma lem7000193 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7000194 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1090 A B s y t R x) = (term1091 A B s y t R x).
Proof. exact (MK_COMB (@lem7000193) (@lem7000192 A B s y t R x)). Qed.
Lemma lem7000195 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1087 A B y t R x y') = (term1081 A B y t R x y').
Proof. exact (eq_refl (term1087 A B y t R x y')). Qed.
Lemma lem7000196 {A : Type'} (s : A -> Prop) (x : A) : (term964 A s x) = (term964 A s x).
Proof. exact (eq_refl (term964 A s x)). Qed.
Lemma lem7000197 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1092 A B s y t R x y') = (term1093 A B s y t R x y').
Proof. exact (MK_COMB (@lem7000196 A s x) (@lem7000195 A B y t R x y')). Qed.
Lemma lem7000198 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1094 A B s y t R x) = (term1095 A B s y t R x).
Proof. exact (fun_ext (fun y' : B => @lem7000197 A B s y t R x y')). Qed.
Lemma lem7000199 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7000200 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1086 A B s y t R x) = (term1096 A B s y t R x).
Proof. exact (MK_COMB (@lem7000199 B) (@lem7000198 A B s y t R x)). Qed.
Lemma lem7000201 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : ((term1085 A B s y t R x) = (term1086 A B s y t R x)) = ((term1084 A B s y t R x) = (term1096 A B s y t R x)).
Proof. exact (MK_COMB (@lem7000194 A B s y t R x) (@lem7000200 A B s y t R x)). Qed.
Lemma lem7000202 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1084 A B s y t R x) = (term1096 A B s y t R x).
Proof. exact (EQ_MP (@lem7000201 A B s y t R x) (@lem7000186 A B s y t R x)). Qed.
Lemma lem7000204 {A : Type'} (P : Prop) (Q : A -> Prop) : (term292 A P Q) = (term291 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7000205 {B : Type'} (P : Prop) (Q : B -> Prop) : (term292 B P Q) = (term291 B P Q).
Proof. exact (@lem7000204 B P Q). Qed.
Lemma lem7000206 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1097 A B s y t R x y') = (term1098 A B s y t R x y').
Proof. exact (@lem7000205 B (term963 A s x) (term1080 A B y t R x y')). Qed.
Lemma lem7000207 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term1099 A B y t R x y'' y') = (term1078 A B y t R x y' y'').
Proof. exact (eq_refl (term1099 A B y t R x y'' y')). Qed.
Lemma lem7000208 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1100 A B y t R x y') = (term1080 A B y t R x y').
Proof. exact (fun_ext (fun y'' : B => @lem7000207 A B y t R x y'' y')). Qed.
Lemma lem7000209 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7000210 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1101 A B y t R x y') = (term1081 A B y t R x y').
Proof. exact (MK_COMB (@lem7000209 B) (@lem7000208 A B y t R x y')). Qed.
Lemma lem7000211 {A : Type'} (s : A -> Prop) (x : A) : (term964 A s x) = (term964 A s x).
Proof. exact (eq_refl (term964 A s x)). Qed.
Lemma lem7000212 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1097 A B s y t R x y') = (term1093 A B s y t R x y').
Proof. exact (MK_COMB (@lem7000211 A s x) (@lem7000210 A B y t R x y')). Qed.
Lemma lem7000213 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7000214 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1102 A B s y t R x y') = (term1103 A B s y t R x y').
Proof. exact (MK_COMB (@lem7000213) (@lem7000212 A B s y t R x y')). Qed.
Lemma lem7000215 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term1099 A B y t R x y'' y') = (term1078 A B y t R x y' y'').
Proof. exact (eq_refl (term1099 A B y t R x y'' y')). Qed.
Lemma lem7000216 {A : Type'} (s : A -> Prop) (x : A) : (term964 A s x) = (term964 A s x).
Proof. exact (eq_refl (term964 A s x)). Qed.
Lemma lem7000217 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term1104 A B s y t R x y'' y') = (term1105 A B s y t R x y' y'').
Proof. exact (MK_COMB (@lem7000216 A s x) (@lem7000215 A B y t R x y' y'')). Qed.
Lemma lem7000218 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1106 A B s y t R x y') = (term1107 A B s y t R x y').
Proof. exact (fun_ext (fun y'' : B => @lem7000217 A B s y t R x y'' y')). Qed.
Lemma lem7000219 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7000220 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1098 A B s y t R x y') = (term1108 A B s y t R x y').
Proof. exact (MK_COMB (@lem7000219 B) (@lem7000218 A B s y t R x y')). Qed.
Lemma lem7000221 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : ((term1097 A B s y t R x y') = (term1098 A B s y t R x y')) = ((term1093 A B s y t R x y') = (term1108 A B s y t R x y')).
Proof. exact (MK_COMB (@lem7000214 A B s y t R x y') (@lem7000220 A B s y t R x y')). Qed.
Lemma lem7000222 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1093 A B s y t R x y') = (term1108 A B s y t R x y').
Proof. exact (EQ_MP (@lem7000221 A B s y t R x y') (@lem7000206 A B s y t R x y')). Qed.
Lemma lem7000223 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1095 A B s y t R x) = (term1109 A B s y t R x).
Proof. exact (fun_ext (fun y' : B => @lem7000222 A B s y t R x y')). Qed.
Lemma lem7000224 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7000225 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1096 A B s y t R x) = (term1110 A B s y t R x).
Proof. exact (MK_COMB (@lem7000224 B) (@lem7000223 A B s y t R x)). Qed.
Lemma lem7000226 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1084 A B s y t R x) = (term1110 A B s y t R x).
Proof. exact (TRANS (@lem7000202 A B s y t R x) (@lem7000225 A B s y t R x)). Qed.
Lemma lem7000227 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1008 A B s y t R x) = (term1110 A B s y t R x).
Proof. exact (TRANS (@lem7000182 A B s y t R x) (@lem7000226 A B s y t R x)). Qed.
Lemma lem7000228 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term1009 A B s y t R) = (term1111 A B s y t R).
Proof. exact (fun_ext (fun x : A => @lem7000227 A B s y t R x)). Qed.
Lemma lem7000229 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7000230 {A B : Type'} (s : A -> Prop) (y : A -> B) (t : B -> Prop) (R : type1413 A B) : (term1010 A B s y t R) = (term1112 A B s y t R).
Proof. exact (MK_COMB (@lem7000229 A) (@lem7000228 A B s y t R)). Qed.
Lemma lem7000268 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term1105 A B s y t R x y' y'') = (term1113 A B y s t R x y' y'').
Proof. exact (@lem19490 (term1003 A B t R y x) (term963 A s x) (term1051 A B t R x y' y'')). Qed.
Lemma lem7000269 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y : B) : (term1114 A B s t R x y' y) = (term1114 A B s t R x y' y).
Proof. exact (eq_refl (term1114 A B s t R x y' y)). Qed.
Lemma lem7000276 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1115 A B s t R y x) = (term1116 A B t s R y x).
Proof. exact (@lem19490 (term999 A B t y x) (term963 A s x) (term406 A B R y x)). Qed.
Lemma lem7000277 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7000278 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (y : A -> B) (x : A) : (term1117 A B s t R y x) = (term1118 A B t s R y x).
Proof. exact (MK_COMB (@lem7000277) (@lem7000276 A B t s R y x)). Qed.
Lemma lem7000279 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term1113 A B y s t R x y' y'') = (term1119 A B y s t R x y' y'').
Proof. exact (MK_COMB (@lem7000278 A B t s R y x) (@lem7000269 A B s t R x y' y'')). Qed.
Lemma lem7000281 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) (y'' : B) : (term1105 A B s y t R x y' y'') = (term1119 A B y s t R x y' y'').
Proof. exact (TRANS (@lem7000268 A B y s t R x y' y'') (@lem7000279 A B y s t R x y' y'')). Qed.
Lemma lem7000282 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1107 A B s y t R x y') = (term1120 A B y s t R x y').
Proof. exact (fun_ext (fun y'' : B => @lem7000281 A B y s t R x y'' y')). Qed.
Lemma lem7000283 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7000284 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) (y' : B) : (term1108 A B s y t R x y') = (term1121 A B y s t R x y').
Proof. exact (MK_COMB (@lem7000283 B) (@lem7000282 A B y s t R x y')). Qed.
Lemma lem7000285 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1109 A B s y t R x) = (term1122 A B y s t R x).
Proof. exact (fun_ext (fun y' : B => @lem7000284 A B y s t R x y')). Qed.
Lemma lem7000286 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7000287 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term1110 A B s y t R x) = (term1123 A B y s t R x).
Proof. exact (MK_COMB (@lem7000286 B) (@lem7000285 A B y s t R x)). Qed.
Lemma lem7000288 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term1111 A B s y t R) = (term1124 A B y s t R).
Proof. exact (fun_ext (fun x : A => @lem7000287 A B y s t R x)). Qed.
Lemma lem7000289 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7000290 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term1112 A B s y t R) = (term1125 A B y s t R).
Proof. exact (MK_COMB (@lem7000289 A) (@lem7000288 A B y s t R)). Qed.
Lemma lem7000291 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term1010 A B s y t R) = (term1125 A B y s t R).
Proof. exact (TRANS (@lem7000230 A B s y t R) (@lem7000290 A B y s t R)). Qed.
Lemma lem7000292 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1125 A B y s t R.
Proof. exact (EQ_MP (@lem7000291 A B y s t R) (@lem6999206 A B x y t R s h1)). Qed.
Lemma lem7000308 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) (h1 : term380 A B R x' x) : term380 A B R x' x.
Proof. exact (h1). Qed.
Lemma lem7000330 {A B : Type'} (_93312 : B -> Prop) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1126 A B _93304 _93312.
Proof. exact (@lem6999562 A B _93304 h1 _93312). Qed.
Lemma lem7000331 {A B : Type'} (_93304 : type830 A B) (_93312 : B -> Prop) : (term1126 A B _93304 _93312) = (term1040 A B _93304 _93312).
Proof. exact (eq_refl (term1126 A B _93304 _93312)). Qed.
Lemma lem7000332 {A B : Type'} (_93312 : B -> Prop) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1040 A B _93304 _93312.
Proof. exact (EQ_MP (@lem7000331 A B _93304 _93312) (@lem7000330 A B _93312 _93304 h1)). Qed.
Lemma lem7000333 {A B : Type'} (_93312 : B -> Prop) (_93313 : type1413 A B) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1127 A B _93304 _93312 _93313.
Proof. exact (@lem7000332 A B _93312 _93304 h1 _93313). Qed.
Lemma lem7000334 {A B : Type'} (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) : (term1127 A B _93304 _93312 _93313) = (term1038 A B _93304 _93312 _93313).
Proof. exact (eq_refl (term1127 A B _93304 _93312 _93313)). Qed.
Lemma lem7000335 {A B : Type'} (_93312 : B -> Prop) (_93313 : type1413 A B) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1038 A B _93304 _93312 _93313.
Proof. exact (EQ_MP (@lem7000334 A B _93304 _93312 _93313) (@lem7000333 A B _93312 _93313 _93304 h1)). Qed.
Lemma lem7000336 {A B : Type'} (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1128 A B _93304 _93312 _93313 _93314.
Proof. exact (@lem7000335 A B _93312 _93313 _93304 h1 _93314). Qed.
Lemma lem7000337 {A B : Type'} (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) : (term1128 A B _93304 _93312 _93313 _93314) = (term1036 A B _93304 _93312 _93313 _93314).
Proof. exact (eq_refl (term1128 A B _93304 _93312 _93313 _93314)). Qed.
Lemma lem7000338 {A B : Type'} (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1036 A B _93304 _93312 _93313 _93314.
Proof. exact (EQ_MP (@lem7000337 A B _93304 _93312 _93313 _93314) (@lem7000336 A B _93312 _93313 _93314 _93304 h1)). Qed.
Lemma lem7000339 {A B : Type'} (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1129 A B _93304 _93312 _93313 _93314 _93315.
Proof. exact (@lem7000338 A B _93312 _93313 _93314 _93304 h1 _93315). Qed.
Lemma lem7000340 {A B : Type'} (_93315 : B) (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) : (term1129 A B _93304 _93312 _93313 _93314 _93315) = (term1034 A B _93315 _93304 _93312 _93313 _93314).
Proof. exact (eq_refl (term1129 A B _93304 _93312 _93313 _93314 _93315)). Qed.
Lemma lem7000341 {A B : Type'} (_93315 : B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1034 A B _93315 _93304 _93312 _93313 _93314.
Proof. exact (EQ_MP (@lem7000340 A B _93315 _93304 _93312 _93313 _93314) (@lem7000339 A B _93312 _93313 _93314 _93315 _93304 h1)). Qed.
Lemma lem7000342 {A B : Type'} (_93316 : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1130 A B y s t R _93316.
Proof. exact (@lem6999748 A B x y t R s h1 _93316). Qed.
Lemma lem7000343 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_93316 : A) : (term1130 A B y s t R _93316) = (term1123 A B y s t R _93316).
Proof. exact (eq_refl (term1130 A B y s t R _93316)). Qed.
Lemma lem7000344 {A B : Type'} (_93316 : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1123 A B y s t R _93316.
Proof. exact (EQ_MP (@lem7000343 A B y s t R _93316) (@lem7000342 A B _93316 x y t R s h1)). Qed.
Lemma lem7000345 {A B : Type'} (_93316 : A) (_93317 : B) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1131 A B y s t R _93316 _93317.
Proof. exact (@lem7000344 A B _93316 x y t R s h1 _93317). Qed.
Lemma lem7000346 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_93316 : A) (_93317 : B) : (term1131 A B y s t R _93316 _93317) = (term1121 A B y s t R _93316 _93317).
Proof. exact (eq_refl (term1131 A B y s t R _93316 _93317)). Qed.
Lemma lem7000347 {A B : Type'} (_93316 : A) (_93317 : B) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1121 A B y s t R _93316 _93317.
Proof. exact (EQ_MP (@lem7000346 A B y s t R _93316 _93317) (@lem7000345 A B _93316 _93317 x y t R s h1)). Qed.
Lemma lem7000348 {A B : Type'} (_93316 : A) (_93317 : B) (_93318 : B) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1132 A B y s t R _93316 _93317 _93318.
Proof. exact (@lem7000347 A B _93316 _93317 x y t R s h1 _93318). Qed.
Lemma lem7000349 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_93316 : A) (_93318 : B) (_93317 : B) : (term1132 A B y s t R _93316 _93317 _93318) = (term1119 A B y s t R _93316 _93318 _93317).
Proof. exact (eq_refl (term1132 A B y s t R _93316 _93317 _93318)). Qed.
Lemma lem7000350 {A B : Type'} (_93316 : A) (_93318 : B) (_93317 : B) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1119 A B y s t R _93316 _93318 _93317.
Proof. exact (EQ_MP (@lem7000349 A B y s t R _93316 _93318 _93317) (@lem7000348 A B _93316 _93317 _93318 x y t R s h1)). Qed.
Lemma lem7000372 {A B : Type'} (_93326 : B -> Prop) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1126 A B _93304 _93326.
Proof. exact (@lem7000106 A B _93304 h1 _93326). Qed.
Lemma lem7000373 {A B : Type'} (_93304 : type830 A B) (_93326 : B -> Prop) : (term1126 A B _93304 _93326) = (term1040 A B _93304 _93326).
Proof. exact (eq_refl (term1126 A B _93304 _93326)). Qed.
Lemma lem7000374 {A B : Type'} (_93326 : B -> Prop) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1040 A B _93304 _93326.
Proof. exact (EQ_MP (@lem7000373 A B _93304 _93326) (@lem7000372 A B _93326 _93304 h1)). Qed.
Lemma lem7000375 {A B : Type'} (_93326 : B -> Prop) (_93327 : type1413 A B) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1127 A B _93304 _93326 _93327.
Proof. exact (@lem7000374 A B _93326 _93304 h1 _93327). Qed.
Lemma lem7000376 {A B : Type'} (_93304 : type830 A B) (_93326 : B -> Prop) (_93327 : type1413 A B) : (term1127 A B _93304 _93326 _93327) = (term1038 A B _93304 _93326 _93327).
Proof. exact (eq_refl (term1127 A B _93304 _93326 _93327)). Qed.
Lemma lem7000377 {A B : Type'} (_93326 : B -> Prop) (_93327 : type1413 A B) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1038 A B _93304 _93326 _93327.
Proof. exact (EQ_MP (@lem7000376 A B _93304 _93326 _93327) (@lem7000375 A B _93326 _93327 _93304 h1)). Qed.
Lemma lem7000378 {A B : Type'} (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1128 A B _93304 _93326 _93327 _93328.
Proof. exact (@lem7000377 A B _93326 _93327 _93304 h1 _93328). Qed.
Lemma lem7000379 {A B : Type'} (_93304 : type830 A B) (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) : (term1128 A B _93304 _93326 _93327 _93328) = (term1036 A B _93304 _93326 _93327 _93328).
Proof. exact (eq_refl (term1128 A B _93304 _93326 _93327 _93328)). Qed.
Lemma lem7000380 {A B : Type'} (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1036 A B _93304 _93326 _93327 _93328.
Proof. exact (EQ_MP (@lem7000379 A B _93304 _93326 _93327 _93328) (@lem7000378 A B _93326 _93327 _93328 _93304 h1)). Qed.
Lemma lem7000381 {A B : Type'} (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) (_93329 : B) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1129 A B _93304 _93326 _93327 _93328 _93329.
Proof. exact (@lem7000380 A B _93326 _93327 _93328 _93304 h1 _93329). Qed.
Lemma lem7000382 {A B : Type'} (_93329 : B) (_93304 : type830 A B) (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) : (term1129 A B _93304 _93326 _93327 _93328 _93329) = (term1034 A B _93329 _93304 _93326 _93327 _93328).
Proof. exact (eq_refl (term1129 A B _93304 _93326 _93327 _93328 _93329)). Qed.
Lemma lem7000383 {A B : Type'} (_93329 : B) (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1034 A B _93329 _93304 _93326 _93327 _93328.
Proof. exact (EQ_MP (@lem7000382 A B _93329 _93304 _93326 _93327 _93328) (@lem7000381 A B _93326 _93327 _93328 _93329 _93304 h1)). Qed.
Lemma lem7000384 {A B : Type'} (_93330 : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1130 A B y s t R _93330.
Proof. exact (@lem7000292 A B x y t R s h1 _93330). Qed.
Lemma lem7000385 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_93330 : A) : (term1130 A B y s t R _93330) = (term1123 A B y s t R _93330).
Proof. exact (eq_refl (term1130 A B y s t R _93330)). Qed.
Lemma lem7000386 {A B : Type'} (_93330 : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1123 A B y s t R _93330.
Proof. exact (EQ_MP (@lem7000385 A B y s t R _93330) (@lem7000384 A B _93330 x y t R s h1)). Qed.
Lemma lem7000387 {A B : Type'} (_93330 : A) (_93331 : B) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1131 A B y s t R _93330 _93331.
Proof. exact (@lem7000386 A B _93330 x y t R s h1 _93331). Qed.
Lemma lem7000388 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_93330 : A) (_93331 : B) : (term1131 A B y s t R _93330 _93331) = (term1121 A B y s t R _93330 _93331).
Proof. exact (eq_refl (term1131 A B y s t R _93330 _93331)). Qed.
Lemma lem7000389 {A B : Type'} (_93330 : A) (_93331 : B) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1121 A B y s t R _93330 _93331.
Proof. exact (EQ_MP (@lem7000388 A B y s t R _93330 _93331) (@lem7000387 A B _93330 _93331 x y t R s h1)). Qed.
Lemma lem7000390 {A B : Type'} (_93330 : A) (_93331 : B) (_93332 : B) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1132 A B y s t R _93330 _93331 _93332.
Proof. exact (@lem7000389 A B _93330 _93331 x y t R s h1 _93332). Qed.
Lemma lem7000391 {A B : Type'} (y : A -> B) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_93330 : A) (_93332 : B) (_93331 : B) : (term1132 A B y s t R _93330 _93331 _93332) = (term1119 A B y s t R _93330 _93332 _93331).
Proof. exact (eq_refl (term1132 A B y s t R _93330 _93331 _93332)). Qed.
Lemma lem7000392 {A B : Type'} (_93330 : A) (_93332 : B) (_93331 : B) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1119 A B y s t R _93330 _93332 _93331.
Proof. exact (EQ_MP (@lem7000391 A B y s t R _93330 _93332 _93331) (@lem7000390 A B _93330 _93331 _93332 x y t R s h1)). Qed.
Lemma lem7000399 {A B : Type'} (_93316 : A) (_93318 : B) (_93317 : B) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1114 A B s t R _93316 _93318 _93317.
Proof. exact (proj2 (@lem7000350 A B _93316 _93318 _93317 x y t R s h1)). Qed.
Lemma lem7000403 {A B : Type'} (_93315 : B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1133 A B _93315 _93304 _93312 _93313 _93314.
Proof. exact (proj2 (@lem7000341 A B _93315 _93312 _93313 _93314 _93304 h1)). Qed.
Lemma lem7000404 {A B : Type'} (_93315 : B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1134 A B _93315 _93304 _93312 _93313 _93314.
Proof. exact (proj1 (@lem7000341 A B _93315 _93312 _93313 _93314 _93304 h1)). Qed.
Lemma lem7000412 {A B : Type'} (_93330 : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1116 A B t s R y _93330.
Proof. exact (proj1 (@lem7000392 A B _93330 (@el B) (@el B) x y t R s h1)). Qed.
Lemma lem7000415 {A B : Type'} (_93329 : B) (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1133 A B _93329 _93304 _93326 _93327 _93328.
Proof. exact (proj2 (@lem7000383 A B _93329 _93326 _93327 _93328 _93304 h1)). Qed.
Lemma lem7000426 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term963 A s x') : term963 A s x'.
Proof. exact (h1). Qed.
Lemma lem7000498 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term983 A B _93304 t R x' x) : term983 A B _93304 t R x' x.
Proof. exact (h1). Qed.
Lemma lem7000509 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_93316 : A) (_93318 : B) (_93317 : B) : (term991 A B t R _93316 _93318 _93317) = (term1135 A B t R _93316 _93318 _93317).
Proof. exact (@lem6997368 (term963 B t _93318) (term380 A B R _93316 _93318) (_93318 = _93317)). Qed.
Lemma lem7000510 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_93316 : A) (_93317 : B) : (term990 A B t R _93316 _93317) = (term990 A B t R _93316 _93317).
Proof. exact (eq_refl (term990 A B t R _93316 _93317)). Qed.
Lemma lem7000511 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_93316 : A) (_93318 : B) (_93317 : B) : (term1051 A B t R _93316 _93318 _93317) = (term1136 A B t R _93316 _93318 _93317).
Proof. exact (MK_COMB (@lem7000510 A B t R _93316 _93317) (@lem7000509 A B t R _93316 _93318 _93317)). Qed.
Lemma lem7000518 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_93316 : A) (_93318 : B) (_93317 : B) : (term1136 A B t R _93316 _93318 _93317) = (term1137 A B t R _93316 _93318 _93317).
Proof. exact (@lem6997368 (term963 B t _93317) (term380 A B R _93316 _93317) (term1135 A B t R _93316 _93318 _93317)). Qed.
Lemma lem7000519 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_93316 : A) (_93318 : B) (_93317 : B) : (term1051 A B t R _93316 _93318 _93317) = (term1137 A B t R _93316 _93318 _93317).
Proof. exact (TRANS (@lem7000511 A B t R _93316 _93318 _93317) (@lem7000518 A B t R _93316 _93318 _93317)). Qed.
Lemma lem7000520 {A : Type'} (s : A -> Prop) (_93316 : A) : (term964 A s _93316) = (term964 A s _93316).
Proof. exact (eq_refl (term964 A s _93316)). Qed.
Lemma lem7000523 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_93316 : A) (_93318 : B) (_93317 : B) : (term1114 A B s t R _93316 _93318 _93317) = (term1138 A B s t R _93316 _93318 _93317).
Proof. exact (MK_COMB (@lem7000520 A s _93316) (@lem7000519 A B t R _93316 _93318 _93317)). Qed.
Lemma lem7000524 {A B : Type'} (_93316 : A) (_93318 : B) (_93317 : B) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1138 A B s t R _93316 _93318 _93317.
Proof. exact (EQ_MP (@lem7000523 A B s t R _93316 _93318 _93317) (@lem7000399 A B _93316 _93318 _93317 x y t R s h1)). Qed.
Lemma lem7000547 {A B : Type'} (_93315 : B) (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) : (term1134 A B _93315 _93304 _93312 _93313 _93314) = (term1139 A B _93315 _93304 _93312 _93313 _93314).
Proof. exact (@lem6997368 (term963 B _93312 _93315) (term380 A B _93313 _93314 _93315) (term960 A B _93304 _93312 _93313 _93314)). Qed.
Lemma lem7000548 {A B : Type'} (_93315 : B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1139 A B _93315 _93304 _93312 _93313 _93314.
Proof. exact (EQ_MP (@lem7000547 A B _93315 _93304 _93312 _93313 _93314) (@lem7000404 A B _93315 _93312 _93313 _93314 _93304 h1)). Qed.
Lemma lem7000559 {A B : Type'} (_93315 : B) (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) : (term1133 A B _93315 _93304 _93312 _93313 _93314) = (term1140 A B _93315 _93304 _93312 _93313 _93314).
Proof. exact (@lem6997368 (term963 B _93312 _93315) (term380 A B _93313 _93314 _93315) (term370 A B _93304 _93312 _93313 _93314)). Qed.
Lemma lem7000560 {A B : Type'} (_93315 : B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1140 A B _93315 _93304 _93312 _93313 _93314.
Proof. exact (EQ_MP (@lem7000559 A B _93315 _93304 _93312 _93313 _93314) (@lem7000403 A B _93315 _93312 _93313 _93314 _93304 h1)). Qed.
Lemma lem7000570 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term963 A s x') : term963 A s x'.
Proof. exact (h1). Qed.
Lemma lem7000640 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _93304 t R x' x) : (term367 A B _93304 t R x') = x.
Proof. exact (proj2 (@lem6999215 A B s _93304 t R x' x h1)). Qed.
Lemma lem7000642 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) (h1 : term380 A B R x' x) : term380 A B R x' x.
Proof. exact (h1). Qed.
Lemma lem7000703 {A B : Type'} (_93329 : B) (_93304 : type830 A B) (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) : (term1133 A B _93329 _93304 _93326 _93327 _93328) = (term1140 A B _93329 _93304 _93326 _93327 _93328).
Proof. exact (@lem6997368 (term963 B _93326 _93329) (term380 A B _93327 _93328 _93329) (term370 A B _93304 _93326 _93327 _93328)). Qed.
Lemma lem7000774 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term963 A s x') : term963 A s x'.
Proof. exact (h1). Qed.
Lemma lem7000845 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _93304 t R x' x) : x = (term367 A B _93304 t R x').
Proof. exact (SYM (@lem7000640 A B s _93304 t R x' x h1)). Qed.
Lemma lem7000901 {A B : Type'} (R : type1413 A B) (x' : A) : (term1141 A B R x') = (term1141 A B R x').
Proof. exact (eq_refl (term1141 A B R x')). Qed.
Lemma lem7000902 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _93304 t R x' x) : (term1142 A B R x' x) = (term1143 A B _93304 t R x').
Proof. exact (MK_COMB (@lem7000901 A B R x') (@lem7000845 A B s _93304 t R x' x h1)). Qed.
Lemma lem7000903 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term1143 A B _93304 t R x') = (term1144 A B _93304 t R x').
Proof. exact (eq_refl (term1143 A B _93304 t R x')). Qed.
Lemma lem7000904 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) : (term1145 A B R x' x) = (term1145 A B R x' x).
Proof. exact (eq_refl (term1145 A B R x' x)). Qed.
Lemma lem7000905 {A B : Type'} (x : B) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : ((term1142 A B R x' x) = (term1143 A B _93304 t R x')) = ((term1142 A B R x' x) = (term1144 A B _93304 t R x')).
Proof. exact (MK_COMB (@lem7000904 A B R x' x) (@lem7000903 A B _93304 t R x')). Qed.
Lemma lem7000906 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) : (term1142 A B R x' x) = (term380 A B R x' x).
Proof. exact (eq_refl (term1142 A B R x' x)). Qed.
Lemma lem7000907 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7000908 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) : (term1145 A B R x' x) = (term1146 A B R x' x).
Proof. exact (MK_COMB (@lem7000907) (@lem7000906 A B R x' x)). Qed.
Lemma lem7000909 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term1144 A B _93304 t R x') = (term1144 A B _93304 t R x').
Proof. exact (eq_refl (term1144 A B _93304 t R x')). Qed.
Lemma lem7000910 {A B : Type'} (x : B) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : ((term1142 A B R x' x) = (term1144 A B _93304 t R x')) = ((term380 A B R x' x) = (term1144 A B _93304 t R x')).
Proof. exact (MK_COMB (@lem7000908 A B R x' x) (@lem7000909 A B _93304 t R x')). Qed.
Lemma lem7000911 {A B : Type'} (x : B) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : ((term1142 A B R x' x) = (term1143 A B _93304 t R x')) = ((term380 A B R x' x) = (term1144 A B _93304 t R x')).
Proof. exact (TRANS (@lem7000905 A B x _93304 t R x') (@lem7000910 A B x _93304 t R x')). Qed.
Lemma lem7000912 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _93304 t R x' x) : (term380 A B R x' x) = (term1144 A B _93304 t R x').
Proof. exact (EQ_MP (@lem7000911 A B x _93304 t R x') (@lem7000902 A B s _93304 t R x' x h1)). Qed.
Lemma lem7000913 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term380 A B R x' x) (h2 : term981 A B s _93304 t R x' x) : term1144 A B _93304 t R x'.
Proof. exact (EQ_MP (@lem7000912 A B s _93304 t R x' x h2) (@lem7000642 A B R x' x h1)). Qed.
Lemma lem7000941 {A B : Type'} (_93330 : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1147 A B s t y _93330.
Proof. exact (proj1 (@lem7000412 A B _93330 x y t R s h1)). Qed.
Lemma lem7000955 {A B : Type'} (_93330 : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1148 A B s R y _93330.
Proof. exact (proj2 (@lem7000412 A B _93330 x y t R s h1)). Qed.
Lemma lem7000983 {A B : Type'} (_93329 : B) (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1140 A B _93329 _93304 _93326 _93327 _93328.
Proof. exact (EQ_MP (@lem7000703 A B _93329 _93304 _93326 _93327 _93328) (@lem7000415 A B _93329 _93326 _93327 _93328 _93304 h1)). Qed.
Lemma lem7001120 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _93304 t R x' x) : @I (A -> Prop) s x'.
Proof. exact (proj1 (@lem6999210 A B s _93304 t R x' x h1)). Qed.
Lemma lem7001121 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _93304 t R x' x) : term1149 A s x'.
Proof. exact (fun h0 : term963 A s x' => @lem7001120 A B s _93304 t R x' x h1). Qed.
Lemma lem7001123 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7001124 {A : Type'} (s : A -> Prop) (x' : A) : (term1149 A s x') = (@I (A -> Prop) s x').
Proof. exact (@lem7001123 (@I (A -> Prop) s x')). Qed.
Lemma lem7001125 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _93304 t R x' x) : @I (A -> Prop) s x'.
Proof. exact (EQ_MP (@lem7001124 A s x') (@lem7001121 A B s _93304 t R x' x h1)). Qed.
Lemma lem7001128 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7001130 {A : Type'} (s : A -> Prop) (x' : A) : (term963 A s x') = (term1150 A s x').
Proof. exact (@lem7001128 (@I (A -> Prop) s x')). Qed.
Lemma lem7001133 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term963 A s x') : term1150 A s x'.
Proof. exact (EQ_MP (@lem7001130 A s x') (@lem7000426 A s x' h1)). Qed.
Lemma lem7001136 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term987 A B s _93304 t R x' x) : False.
Proof. exact (@lem7001133 A s x' h1 (@lem7001125 A B s _93304 t R x' x h2)). Qed.
Lemma lem7001137 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term987 A B s _93304 t R x' x) : term596.
Proof. exact (fun h0 : ~ False => @lem7001136 A B s _93304 t R x' x h1 h2). Qed.
Lemma lem7001139 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7001140 : term596 = False.
Proof. exact (@lem7001139 False). Qed.
Lemma lem7001141 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term987 A B s _93304 t R x' x) : False.
Proof. exact (EQ_MP (@lem7001140) (@lem7001137 A B s _93304 t R x' x h1 h2)). Qed.
Lemma lem7001278 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _93304 t R x' x) : @I (A -> Prop) s x'.
Proof. exact (proj1 (@lem6999210 A B s _93304 t R x' x h1)). Qed.
Lemma lem7001279 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _93304 t R x' x) : term1149 A s x'.
Proof. exact (fun h0 : term963 A s x' => @lem7001278 A B s _93304 t R x' x h1). Qed.
Lemma lem7001281 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7001282 {A : Type'} (s : A -> Prop) (x' : A) : (term1149 A s x') = (@I (A -> Prop) s x').
Proof. exact (@lem7001281 (@I (A -> Prop) s x')). Qed.
Lemma lem7001283 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _93304 t R x' x) : @I (A -> Prop) s x'.
Proof. exact (EQ_MP (@lem7001282 A s x') (@lem7001279 A B s _93304 t R x' x h1)). Qed.
Lemma lem7001285 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : @I (B -> Prop) t x.
Proof. exact (proj1 (@lem6999202 A B x y t R s h1)). Qed.
Lemma lem7001286 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1149 B t x.
Proof. exact (fun h0 : term963 B t x => @lem7001285 A B x y t R s h1). Qed.
Lemma lem7001288 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7001289 {B : Type'} (t : B -> Prop) (x : B) : (term1149 B t x) = (@I (B -> Prop) t x).
Proof. exact (@lem7001288 (@I (B -> Prop) t x)). Qed.
Lemma lem7001290 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : @I (B -> Prop) t x.
Proof. exact (EQ_MP (@lem7001289 B t x) (@lem7001286 A B x y t R s h1)). Qed.
Lemma lem7001292 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _93304 t R x' x) : term378 A B R x' x.
Proof. exact (proj2 (@lem6999210 A B s _93304 t R x' x h1)). Qed.
Lemma lem7001293 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _93304 t R x' x) : term1151 A B R x' x.
Proof. exact (fun h0 : term380 A B R x' x => @lem7001292 A B s _93304 t R x' x h1). Qed.
Lemma lem7001295 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7001296 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) : (term1151 A B R x' x) = (term378 A B R x' x).
Proof. exact (@lem7001295 (term378 A B R x' x)). Qed.
Lemma lem7001297 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _93304 t R x' x) : term378 A B R x' x.
Proof. exact (EQ_MP (@lem7001296 A B R x' x) (@lem7001293 A B s _93304 t R x' x h1)). Qed.
Lemma lem7001299 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : @I (B -> Prop) t x.
Proof. exact (proj1 (@lem6999202 A B x y t R s h1)). Qed.
Lemma lem7001300 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1149 B t x.
Proof. exact (fun h0 : term963 B t x => @lem7001299 A B x y t R s h1). Qed.
Lemma lem7001302 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7001303 {B : Type'} (t : B -> Prop) (x : B) : (term1149 B t x) = (@I (B -> Prop) t x).
Proof. exact (@lem7001302 (@I (B -> Prop) t x)). Qed.
Lemma lem7001304 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : @I (B -> Prop) t x.
Proof. exact (EQ_MP (@lem7001303 B t x) (@lem7001300 A B x y t R s h1)). Qed.
Lemma lem7001306 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _93304 t R x' x) : term378 A B R x' x.
Proof. exact (proj2 (@lem6999210 A B s _93304 t R x' x h1)). Qed.
Lemma lem7001307 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _93304 t R x' x) : term1151 A B R x' x.
Proof. exact (fun h0 : term380 A B R x' x => @lem7001306 A B s _93304 t R x' x h1). Qed.
Lemma lem7001309 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7001310 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) : (term1151 A B R x' x) = (term378 A B R x' x).
Proof. exact (@lem7001309 (term378 A B R x' x)). Qed.
Lemma lem7001311 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _93304 t R x' x) : term378 A B R x' x.
Proof. exact (EQ_MP (@lem7001310 A B R x' x) (@lem7001307 A B s _93304 t R x' x h1)). Qed.
Lemma lem7001327 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7001328 {A B : Type'} (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : (term1152 A B _93315 _93304 _93312 _93313 _93314) = (term1153 A B _93304 _93312 _93313 _93314 _93315).
Proof. exact (@lem7001327 (term960 A B _93304 _93312 _93313 _93314) (term380 A B _93313 _93314 _93315)). Qed.
Lemma lem7001334 {B : Type'} (_93312 : B -> Prop) (_93315 : B) : (term964 B _93312 _93315) = (term964 B _93312 _93315).
Proof. exact (eq_refl (term964 B _93312 _93315)). Qed.
Lemma lem7001335 {A B : Type'} (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : (term1139 A B _93315 _93304 _93312 _93313 _93314) = (term1154 A B _93304 _93312 _93313 _93314 _93315).
Proof. exact (MK_COMB (@lem7001334 B _93312 _93315) (@lem7001328 A B _93304 _93312 _93313 _93314 _93315)). Qed.
Lemma lem7001339 (q : Prop) (p : Prop) (r : Prop) : (term21 p q r) = (term21 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7001340 {A B : Type'} (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : (term1154 A B _93304 _93312 _93313 _93314 _93315) = (term1155 A B _93304 _93312 _93313 _93314 _93315).
Proof. exact (@lem7001339 (term960 A B _93304 _93312 _93313 _93314) (term963 B _93312 _93315) (term380 A B _93313 _93314 _93315)). Qed.
Lemma lem7001356 {A B : Type'} (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : (term1139 A B _93315 _93304 _93312 _93313 _93314) = (term1155 A B _93304 _93312 _93313 _93314 _93315).
Proof. exact (TRANS (@lem7001335 A B _93304 _93312 _93313 _93314 _93315) (@lem7001340 A B _93304 _93312 _93313 _93314 _93315)). Qed.
Lemma lem7001357 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7001358 {A B : Type'} (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : (term1156 A B _93315 _93304 _93312 _93313 _93314) = (term1157 A B _93304 _93312 _93313 _93314 _93315).
Proof. exact (MK_COMB (@lem7001357) (@lem7001356 A B _93304 _93312 _93313 _93314 _93315)). Qed.
Lemma lem7001374 {A B : Type'} (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : (term1155 A B _93304 _93312 _93313 _93314 _93315) = (term1155 A B _93304 _93312 _93313 _93314 _93315).
Proof. exact (eq_refl (term1155 A B _93304 _93312 _93313 _93314 _93315)). Qed.
Lemma lem7001375 {A B : Type'} (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : ((term1139 A B _93315 _93304 _93312 _93313 _93314) = (term1155 A B _93304 _93312 _93313 _93314 _93315)) = ((term1155 A B _93304 _93312 _93313 _93314 _93315) = (term1155 A B _93304 _93312 _93313 _93314 _93315)).
Proof. exact (MK_COMB (@lem7001358 A B _93304 _93312 _93313 _93314 _93315) (@lem7001374 A B _93304 _93312 _93313 _93314 _93315)). Qed.
Lemma lem7001377 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7001378 (x : Prop) : (x = x) = True.
Proof. exact (@lem7001377 Prop x). Qed.
Lemma lem7001379 {A B : Type'} (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : ((term1155 A B _93304 _93312 _93313 _93314 _93315) = (term1155 A B _93304 _93312 _93313 _93314 _93315)) = True.
Proof. exact (@lem7001378 (term1155 A B _93304 _93312 _93313 _93314 _93315)). Qed.
Lemma lem7001380 {A B : Type'} (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : ((term1139 A B _93315 _93304 _93312 _93313 _93314) = (term1155 A B _93304 _93312 _93313 _93314 _93315)) = True.
Proof. exact (TRANS (@lem7001375 A B _93304 _93312 _93313 _93314 _93315) (@lem7001379 A B _93304 _93312 _93313 _93314 _93315)). Qed.
Lemma lem7001381 {A B : Type'} (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : True = ((term1139 A B _93315 _93304 _93312 _93313 _93314) = (term1155 A B _93304 _93312 _93313 _93314 _93315)).
Proof. exact (SYM (@lem7001380 A B _93304 _93312 _93313 _93314 _93315)). Qed.
Lemma lem7001382 {A B : Type'} (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : (term1139 A B _93315 _93304 _93312 _93313 _93314) = (term1155 A B _93304 _93312 _93313 _93314 _93315).
Proof. exact (EQ_MP (@lem7001381 A B _93304 _93312 _93313 _93314 _93315) (@lem0)). Qed.
Lemma lem7001383 {A B : Type'} (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1155 A B _93304 _93312 _93313 _93314 _93315.
Proof. exact (EQ_MP (@lem7001382 A B _93304 _93312 _93313 _93314 _93315) (@lem7000548 A B _93315 _93312 _93313 _93314 _93304 h1)). Qed.
Lemma lem7001385 (b : Prop) (a : Prop) : (a \/ b) = (term555 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7001386 {A B : Type'} (_93315 : B) (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) : (term1155 A B _93304 _93312 _93313 _93314 _93315) = (term1158 A B _93315 _93304 _93312 _93313 _93314).
Proof. exact (@lem7001385 (term965 A B _93312 _93313 _93314 _93315) (term960 A B _93304 _93312 _93313 _93314)). Qed.
Lemma lem7001388 (a : Prop) (b : Prop) : (term582 a b) = (term583 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7001389 {A B : Type'} (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : (term1159 A B _93312 _93313 _93314 _93315) = (term1160 A B _93312 _93313 _93314 _93315).
Proof. exact (@lem7001388 (term963 B _93312 _93315) (term380 A B _93313 _93314 _93315)). Qed.
Lemma lem7001391 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7001392 {B : Type'} (_93312 : B -> Prop) (_93315 : B) : (term1161 B _93312 _93315) = (@I (B -> Prop) _93312 _93315).
Proof. exact (@lem7001391 (@I (B -> Prop) _93312 _93315)). Qed.
Lemma lem7001393 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7001394 {B : Type'} (_93312 : B -> Prop) (_93315 : B) : (term1162 B _93312 _93315) = (term977 B _93312 _93315).
Proof. exact (MK_COMB (@lem7001393) (@lem7001392 B _93312 _93315)). Qed.
Lemma lem7001396 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7001397 {A B : Type'} (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : (term588 A B _93313 _93314 _93315) = (term378 A B _93313 _93314 _93315).
Proof. exact (@lem7001396 (term378 A B _93313 _93314 _93315)). Qed.
Lemma lem7001398 {A B : Type'} (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : (term1160 A B _93312 _93313 _93314 _93315) = (term1163 A B _93312 _93313 _93314 _93315).
Proof. exact (MK_COMB (@lem7001394 B _93312 _93315) (@lem7001397 A B _93313 _93314 _93315)). Qed.
Lemma lem7001399 {A B : Type'} (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : (term1159 A B _93312 _93313 _93314 _93315) = (term1163 A B _93312 _93313 _93314 _93315).
Proof. exact (TRANS (@lem7001389 A B _93312 _93313 _93314 _93315) (@lem7001398 A B _93312 _93313 _93314 _93315)). Qed.
Lemma lem7001400 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7001401 {A B : Type'} (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : (term1164 A B _93312 _93313 _93314 _93315) = (term1165 A B _93312 _93313 _93314 _93315).
Proof. exact (MK_COMB (@lem7001400) (@lem7001399 A B _93312 _93313 _93314 _93315)). Qed.
Lemma lem7001402 {A B : Type'} (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) : (term960 A B _93304 _93312 _93313 _93314) = (term960 A B _93304 _93312 _93313 _93314).
Proof. exact (eq_refl (term960 A B _93304 _93312 _93313 _93314)). Qed.
Lemma lem7001403 {A B : Type'} (_93315 : B) (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) : (term1158 A B _93315 _93304 _93312 _93313 _93314) = (term1166 A B _93315 _93304 _93312 _93313 _93314).
Proof. exact (MK_COMB (@lem7001401 A B _93312 _93313 _93314 _93315) (@lem7001402 A B _93304 _93312 _93313 _93314)). Qed.
Lemma lem7001404 {A B : Type'} (_93315 : B) (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) : (term1155 A B _93304 _93312 _93313 _93314 _93315) = (term1166 A B _93315 _93304 _93312 _93313 _93314).
Proof. exact (TRANS (@lem7001386 A B _93315 _93304 _93312 _93313 _93314) (@lem7001403 A B _93315 _93304 _93312 _93313 _93314)). Qed.
Lemma lem7001406 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term940 A B x y t R s) (h2 : term987 A B s _93304 t R x' x) : term1163 A B t R x' x.
Proof. exact (conj (@lem7001304 A B x y t R s h1) (@lem7001311 A B s _93304 t R x' x h2)). Qed.
Lemma lem7001408 {A B : Type'} (_93315 : B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1166 A B _93315 _93304 _93312 _93313 _93314.
Proof. exact (EQ_MP (@lem7001404 A B _93315 _93304 _93312 _93313 _93314) (@lem7001383 A B _93312 _93313 _93314 _93315 _93304 h1)). Qed.
Lemma lem7001409 {A B : Type'} (_93315 : B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1166 A B _93315 _93304 _93312 _93313 _93314.
Proof. exact (@lem7001408 A B _93315 _93312 _93313 _93314 _93304 h1). Qed.
Lemma lem7001410 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (x' : A) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1166 A B x _93304 t R x'.
Proof. exact (@lem7001409 A B x t R x' _93304 h1). Qed.
Lemma lem7001413 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term940 A B x y t R s) (h3 : term987 A B s _93304 t R x' x) : term960 A B _93304 t R x'.
Proof. exact (@lem7001410 A B x t R x' _93304 h1 (@lem7001406 A B y s _93304 t R x' x h2 h3)). Qed.
Lemma lem7001414 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term940 A B x y t R s) (h3 : term987 A B s _93304 t R x' x) : term1167 A B _93304 t R x'.
Proof. exact (fun h0 : term1168 A B _93304 t R x' => @lem7001413 A B y s _93304 t R x' x h1 h2 h3). Qed.
Lemma lem7001416 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7001417 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term1167 A B _93304 t R x') = (term960 A B _93304 t R x').
Proof. exact (@lem7001416 (term960 A B _93304 t R x')). Qed.
Lemma lem7001418 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term940 A B x y t R s) (h3 : term987 A B s _93304 t R x' x) : term960 A B _93304 t R x'.
Proof. exact (EQ_MP (@lem7001417 A B _93304 t R x') (@lem7001414 A B y s _93304 t R x' x h1 h2 h3)). Qed.
Lemma lem7001420 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : @I (B -> Prop) t x.
Proof. exact (proj1 (@lem6999202 A B x y t R s h1)). Qed.
Lemma lem7001421 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1149 B t x.
Proof. exact (fun h0 : term963 B t x => @lem7001420 A B x y t R s h1). Qed.
Lemma lem7001423 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7001424 {B : Type'} (t : B -> Prop) (x : B) : (term1149 B t x) = (@I (B -> Prop) t x).
Proof. exact (@lem7001423 (@I (B -> Prop) t x)). Qed.
Lemma lem7001425 {A B : Type'} (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : @I (B -> Prop) t x.
Proof. exact (EQ_MP (@lem7001424 B t x) (@lem7001421 A B x y t R s h1)). Qed.
Lemma lem7001427 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _93304 t R x' x) : term378 A B R x' x.
Proof. exact (proj2 (@lem6999210 A B s _93304 t R x' x h1)). Qed.
Lemma lem7001428 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _93304 t R x' x) : term1151 A B R x' x.
Proof. exact (fun h0 : term380 A B R x' x => @lem7001427 A B s _93304 t R x' x h1). Qed.
Lemma lem7001430 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7001431 {A B : Type'} (R : type1413 A B) (x' : A) (x : B) : (term1151 A B R x' x) = (term378 A B R x' x).
Proof. exact (@lem7001430 (term378 A B R x' x)). Qed.
Lemma lem7001432 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term987 A B s _93304 t R x' x) : term378 A B R x' x.
Proof. exact (EQ_MP (@lem7001431 A B R x' x) (@lem7001428 A B s _93304 t R x' x h1)). Qed.
Lemma lem7001448 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7001449 {A B : Type'} (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : (term1169 A B _93315 _93304 _93312 _93313 _93314) = (term1170 A B _93304 _93312 _93313 _93314 _93315).
Proof. exact (@lem7001448 (term370 A B _93304 _93312 _93313 _93314) (term380 A B _93313 _93314 _93315)). Qed.
Lemma lem7001455 {B : Type'} (_93312 : B -> Prop) (_93315 : B) : (term964 B _93312 _93315) = (term964 B _93312 _93315).
Proof. exact (eq_refl (term964 B _93312 _93315)). Qed.
Lemma lem7001456 {A B : Type'} (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : (term1140 A B _93315 _93304 _93312 _93313 _93314) = (term1171 A B _93304 _93312 _93313 _93314 _93315).
Proof. exact (MK_COMB (@lem7001455 B _93312 _93315) (@lem7001449 A B _93304 _93312 _93313 _93314 _93315)). Qed.
Lemma lem7001460 (q : Prop) (p : Prop) (r : Prop) : (term21 p q r) = (term21 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7001461 {A B : Type'} (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : (term1171 A B _93304 _93312 _93313 _93314 _93315) = (term1172 A B _93304 _93312 _93313 _93314 _93315).
Proof. exact (@lem7001460 (term370 A B _93304 _93312 _93313 _93314) (term963 B _93312 _93315) (term380 A B _93313 _93314 _93315)). Qed.
Lemma lem7001477 {A B : Type'} (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : (term1140 A B _93315 _93304 _93312 _93313 _93314) = (term1172 A B _93304 _93312 _93313 _93314 _93315).
Proof. exact (TRANS (@lem7001456 A B _93304 _93312 _93313 _93314 _93315) (@lem7001461 A B _93304 _93312 _93313 _93314 _93315)). Qed.
Lemma lem7001478 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7001479 {A B : Type'} (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : (term1173 A B _93315 _93304 _93312 _93313 _93314) = (term1174 A B _93304 _93312 _93313 _93314 _93315).
Proof. exact (MK_COMB (@lem7001478) (@lem7001477 A B _93304 _93312 _93313 _93314 _93315)). Qed.
Lemma lem7001495 {A B : Type'} (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : (term1172 A B _93304 _93312 _93313 _93314 _93315) = (term1172 A B _93304 _93312 _93313 _93314 _93315).
Proof. exact (eq_refl (term1172 A B _93304 _93312 _93313 _93314 _93315)). Qed.
Lemma lem7001496 {A B : Type'} (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : ((term1140 A B _93315 _93304 _93312 _93313 _93314) = (term1172 A B _93304 _93312 _93313 _93314 _93315)) = ((term1172 A B _93304 _93312 _93313 _93314 _93315) = (term1172 A B _93304 _93312 _93313 _93314 _93315)).
Proof. exact (MK_COMB (@lem7001479 A B _93304 _93312 _93313 _93314 _93315) (@lem7001495 A B _93304 _93312 _93313 _93314 _93315)). Qed.
Lemma lem7001498 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7001499 (x : Prop) : (x = x) = True.
Proof. exact (@lem7001498 Prop x). Qed.
Lemma lem7001500 {A B : Type'} (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : ((term1172 A B _93304 _93312 _93313 _93314 _93315) = (term1172 A B _93304 _93312 _93313 _93314 _93315)) = True.
Proof. exact (@lem7001499 (term1172 A B _93304 _93312 _93313 _93314 _93315)). Qed.
Lemma lem7001501 {A B : Type'} (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : ((term1140 A B _93315 _93304 _93312 _93313 _93314) = (term1172 A B _93304 _93312 _93313 _93314 _93315)) = True.
Proof. exact (TRANS (@lem7001496 A B _93304 _93312 _93313 _93314 _93315) (@lem7001500 A B _93304 _93312 _93313 _93314 _93315)). Qed.
Lemma lem7001502 {A B : Type'} (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : True = ((term1140 A B _93315 _93304 _93312 _93313 _93314) = (term1172 A B _93304 _93312 _93313 _93314 _93315)).
Proof. exact (SYM (@lem7001501 A B _93304 _93312 _93313 _93314 _93315)). Qed.
Lemma lem7001503 {A B : Type'} (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : (term1140 A B _93315 _93304 _93312 _93313 _93314) = (term1172 A B _93304 _93312 _93313 _93314 _93315).
Proof. exact (EQ_MP (@lem7001502 A B _93304 _93312 _93313 _93314 _93315) (@lem0)). Qed.
Lemma lem7001504 {A B : Type'} (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1172 A B _93304 _93312 _93313 _93314 _93315.
Proof. exact (EQ_MP (@lem7001503 A B _93304 _93312 _93313 _93314 _93315) (@lem7000560 A B _93315 _93312 _93313 _93314 _93304 h1)). Qed.
Lemma lem7001506 (b : Prop) (a : Prop) : (a \/ b) = (term555 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7001507 {A B : Type'} (_93315 : B) (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) : (term1172 A B _93304 _93312 _93313 _93314 _93315) = (term1175 A B _93315 _93304 _93312 _93313 _93314).
Proof. exact (@lem7001506 (term965 A B _93312 _93313 _93314 _93315) (term370 A B _93304 _93312 _93313 _93314)). Qed.
Lemma lem7001509 (a : Prop) (b : Prop) : (term582 a b) = (term583 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7001510 {A B : Type'} (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : (term1159 A B _93312 _93313 _93314 _93315) = (term1160 A B _93312 _93313 _93314 _93315).
Proof. exact (@lem7001509 (term963 B _93312 _93315) (term380 A B _93313 _93314 _93315)). Qed.
Lemma lem7001512 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7001513 {B : Type'} (_93312 : B -> Prop) (_93315 : B) : (term1161 B _93312 _93315) = (@I (B -> Prop) _93312 _93315).
Proof. exact (@lem7001512 (@I (B -> Prop) _93312 _93315)). Qed.
Lemma lem7001514 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7001515 {B : Type'} (_93312 : B -> Prop) (_93315 : B) : (term1162 B _93312 _93315) = (term977 B _93312 _93315).
Proof. exact (MK_COMB (@lem7001514) (@lem7001513 B _93312 _93315)). Qed.
Lemma lem7001517 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7001518 {A B : Type'} (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : (term588 A B _93313 _93314 _93315) = (term378 A B _93313 _93314 _93315).
Proof. exact (@lem7001517 (term378 A B _93313 _93314 _93315)). Qed.
Lemma lem7001519 {A B : Type'} (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : (term1160 A B _93312 _93313 _93314 _93315) = (term1163 A B _93312 _93313 _93314 _93315).
Proof. exact (MK_COMB (@lem7001515 B _93312 _93315) (@lem7001518 A B _93313 _93314 _93315)). Qed.
Lemma lem7001520 {A B : Type'} (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : (term1159 A B _93312 _93313 _93314 _93315) = (term1163 A B _93312 _93313 _93314 _93315).
Proof. exact (TRANS (@lem7001510 A B _93312 _93313 _93314 _93315) (@lem7001519 A B _93312 _93313 _93314 _93315)). Qed.
Lemma lem7001521 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7001522 {A B : Type'} (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93315 : B) : (term1164 A B _93312 _93313 _93314 _93315) = (term1165 A B _93312 _93313 _93314 _93315).
Proof. exact (MK_COMB (@lem7001521) (@lem7001520 A B _93312 _93313 _93314 _93315)). Qed.
Lemma lem7001523 {A B : Type'} (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) : (term370 A B _93304 _93312 _93313 _93314) = (term370 A B _93304 _93312 _93313 _93314).
Proof. exact (eq_refl (term370 A B _93304 _93312 _93313 _93314)). Qed.
Lemma lem7001524 {A B : Type'} (_93315 : B) (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) : (term1175 A B _93315 _93304 _93312 _93313 _93314) = (term1176 A B _93315 _93304 _93312 _93313 _93314).
Proof. exact (MK_COMB (@lem7001522 A B _93312 _93313 _93314 _93315) (@lem7001523 A B _93304 _93312 _93313 _93314)). Qed.
Lemma lem7001525 {A B : Type'} (_93315 : B) (_93304 : type830 A B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) : (term1172 A B _93304 _93312 _93313 _93314 _93315) = (term1176 A B _93315 _93304 _93312 _93313 _93314).
Proof. exact (TRANS (@lem7001507 A B _93315 _93304 _93312 _93313 _93314) (@lem7001524 A B _93315 _93304 _93312 _93313 _93314)). Qed.
Lemma lem7001527 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term940 A B x y t R s) (h2 : term987 A B s _93304 t R x' x) : term1163 A B t R x' x.
Proof. exact (conj (@lem7001425 A B x y t R s h1) (@lem7001432 A B s _93304 t R x' x h2)). Qed.
Lemma lem7001529 {A B : Type'} (_93315 : B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1176 A B _93315 _93304 _93312 _93313 _93314.
Proof. exact (EQ_MP (@lem7001525 A B _93315 _93304 _93312 _93313 _93314) (@lem7001504 A B _93312 _93313 _93314 _93315 _93304 h1)). Qed.
Lemma lem7001530 {A B : Type'} (_93315 : B) (_93312 : B -> Prop) (_93313 : type1413 A B) (_93314 : A) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1176 A B _93315 _93304 _93312 _93313 _93314.
Proof. exact (@lem7001529 A B _93315 _93312 _93313 _93314 _93304 h1). Qed.
Lemma lem7001531 {A B : Type'} (x : B) (t : B -> Prop) (R : type1413 A B) (x' : A) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1176 A B x _93304 t R x'.
Proof. exact (@lem7001530 A B x t R x' _93304 h1). Qed.
Lemma lem7001534 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term940 A B x y t R s) (h3 : term987 A B s _93304 t R x' x) : term370 A B _93304 t R x'.
Proof. exact (@lem7001531 A B x t R x' _93304 h1 (@lem7001527 A B y s _93304 t R x' x h2 h3)). Qed.
Lemma lem7001535 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term940 A B x y t R s) (h3 : term987 A B s _93304 t R x' x) : term1177 A B _93304 t R x'.
Proof. exact (fun h0 : term1144 A B _93304 t R x' => @lem7001534 A B y s _93304 t R x' x h1 h2 h3). Qed.
Lemma lem7001537 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7001538 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term1177 A B _93304 t R x') = (term370 A B _93304 t R x').
Proof. exact (@lem7001537 (term370 A B _93304 t R x')). Qed.
Lemma lem7001539 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term940 A B x y t R s) (h3 : term987 A B s _93304 t R x' x) : term370 A B _93304 t R x'.
Proof. exact (EQ_MP (@lem7001538 A B _93304 t R x') (@lem7001535 A B y s _93304 t R x' x h1 h2 h3)). Qed.
Lemma lem7001565 (q : Prop) (p : Prop) (r : Prop) : (term21 p q r) = (term21 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7001566 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_93316 : A) (_93318 : B) (_93317 : B) : (term1178 A B t R _93316 _93318 _93317) = (term1179 A B t R _93316 _93318 _93317).
Proof. exact (@lem7001565 (term963 B t _93318) (term380 A B R _93316 _93317) (term1180 A B R _93316 _93318 _93317)). Qed.
Lemma lem7001590 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7001591 {A B : Type'} (_93317 : B) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1180 A B R _93316 _93318 _93317) = (term1181 A B _93317 R _93316 _93318).
Proof. exact (@lem7001590 (_93318 = _93317) (term380 A B R _93316 _93318)). Qed.
Lemma lem7001599 {A B : Type'} (R : type1413 A B) (_93316 : A) (_93317 : B) : (term573 A B R _93316 _93317) = (term573 A B R _93316 _93317).
Proof. exact (eq_refl (term573 A B R _93316 _93317)). Qed.
Lemma lem7001600 {A B : Type'} (_93317 : B) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1182 A B R _93316 _93318 _93317) = (term1183 A B _93317 R _93316 _93318).
Proof. exact (MK_COMB (@lem7001599 A B R _93316 _93317) (@lem7001591 A B _93317 R _93316 _93318)). Qed.
Lemma lem7001604 (q : Prop) (p : Prop) (r : Prop) : (term21 p q r) = (term21 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7001605 {A B : Type'} (_93317 : B) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1183 A B _93317 R _93316 _93318) = (term1184 A B _93317 R _93316 _93318).
Proof. exact (@lem7001604 (_93318 = _93317) (term380 A B R _93316 _93317) (term380 A B R _93316 _93318)). Qed.
Lemma lem7001623 {A B : Type'} (_93317 : B) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1182 A B R _93316 _93318 _93317) = (term1184 A B _93317 R _93316 _93318).
Proof. exact (TRANS (@lem7001600 A B _93317 R _93316 _93318) (@lem7001605 A B _93317 R _93316 _93318)). Qed.
Lemma lem7001624 {B : Type'} (t : B -> Prop) (_93318 : B) : (term964 B t _93318) = (term964 B t _93318).
Proof. exact (eq_refl (term964 B t _93318)). Qed.
Lemma lem7001625 {A B : Type'} (t : B -> Prop) (_93317 : B) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1179 A B t R _93316 _93318 _93317) = (term1185 A B t _93317 R _93316 _93318).
Proof. exact (MK_COMB (@lem7001624 B t _93318) (@lem7001623 A B _93317 R _93316 _93318)). Qed.
Lemma lem7001629 (q : Prop) (p : Prop) (r : Prop) : (term21 p q r) = (term21 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7001630 {A B : Type'} (t : B -> Prop) (_93317 : B) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1185 A B t _93317 R _93316 _93318) = (term1186 A B t _93317 R _93316 _93318).
Proof. exact (@lem7001629 (_93318 = _93317) (term963 B t _93318) (term1187 A B _93317 R _93316 _93318)). Qed.
Lemma lem7001658 {A B : Type'} (t : B -> Prop) (_93317 : B) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1179 A B t R _93316 _93318 _93317) = (term1186 A B t _93317 R _93316 _93318).
Proof. exact (TRANS (@lem7001625 A B t _93317 R _93316 _93318) (@lem7001630 A B t _93317 R _93316 _93318)). Qed.
Lemma lem7001659 {A B : Type'} (t : B -> Prop) (_93317 : B) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1178 A B t R _93316 _93318 _93317) = (term1186 A B t _93317 R _93316 _93318).
Proof. exact (TRANS (@lem7001566 A B t R _93316 _93318 _93317) (@lem7001658 A B t _93317 R _93316 _93318)). Qed.
Lemma lem7001660 {B : Type'} (t : B -> Prop) (_93317 : B) : (term964 B t _93317) = (term964 B t _93317).
Proof. exact (eq_refl (term964 B t _93317)). Qed.
Lemma lem7001661 {A B : Type'} (t : B -> Prop) (_93317 : B) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1137 A B t R _93316 _93318 _93317) = (term1188 A B t _93317 R _93316 _93318).
Proof. exact (MK_COMB (@lem7001660 B t _93317) (@lem7001659 A B t _93317 R _93316 _93318)). Qed.
Lemma lem7001665 (q : Prop) (p : Prop) (r : Prop) : (term21 p q r) = (term21 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7001666 {A B : Type'} (t : B -> Prop) (_93317 : B) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1188 A B t _93317 R _93316 _93318) = (term1189 A B t _93317 R _93316 _93318).
Proof. exact (@lem7001665 (_93318 = _93317) (term963 B t _93317) (term1190 A B t _93317 R _93316 _93318)). Qed.
Lemma lem7001704 {A B : Type'} (t : B -> Prop) (_93317 : B) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1137 A B t R _93316 _93318 _93317) = (term1189 A B t _93317 R _93316 _93318).
Proof. exact (TRANS (@lem7001661 A B t _93317 R _93316 _93318) (@lem7001666 A B t _93317 R _93316 _93318)). Qed.
Lemma lem7001705 {A : Type'} (s : A -> Prop) (_93316 : A) : (term964 A s _93316) = (term964 A s _93316).
Proof. exact (eq_refl (term964 A s _93316)). Qed.
Lemma lem7001706 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (_93317 : B) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1138 A B s t R _93316 _93318 _93317) = (term1191 A B s t _93317 R _93316 _93318).
Proof. exact (MK_COMB (@lem7001705 A s _93316) (@lem7001704 A B t _93317 R _93316 _93318)). Qed.
Lemma lem7001710 (q : Prop) (p : Prop) (r : Prop) : (term21 p q r) = (term21 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7001711 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (_93317 : B) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1191 A B s t _93317 R _93316 _93318) = (term1192 A B s t _93317 R _93316 _93318).
Proof. exact (@lem7001710 (_93318 = _93317) (term963 A s _93316) (term1193 A B t _93317 R _93316 _93318)). Qed.
Lemma lem7001759 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (_93317 : B) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1138 A B s t R _93316 _93318 _93317) = (term1192 A B s t _93317 R _93316 _93318).
Proof. exact (TRANS (@lem7001706 A B s t _93317 R _93316 _93318) (@lem7001711 A B s t _93317 R _93316 _93318)). Qed.
Lemma lem7001760 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7001761 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (_93317 : B) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1194 A B s t R _93316 _93318 _93317) = (term1195 A B s t _93317 R _93316 _93318).
Proof. exact (MK_COMB (@lem7001760) (@lem7001759 A B s t _93317 R _93316 _93318)). Qed.
Lemma lem7001797 (q : Prop) (p : Prop) (r : Prop) : (term21 p q r) = (term21 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7001798 {A B : Type'} (t : B -> Prop) (_93317 : B) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1196 A B _93317 t R _93316 _93318) = (term1190 A B t _93317 R _93316 _93318).
Proof. exact (@lem7001797 (term963 B t _93318) (term380 A B R _93316 _93317) (term380 A B R _93316 _93318)). Qed.
Lemma lem7001814 {B : Type'} (t : B -> Prop) (_93317 : B) : (term964 B t _93317) = (term964 B t _93317).
Proof. exact (eq_refl (term964 B t _93317)). Qed.
Lemma lem7001815 {A B : Type'} (t : B -> Prop) (_93317 : B) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1197 A B _93317 t R _93316 _93318) = (term1193 A B t _93317 R _93316 _93318).
Proof. exact (MK_COMB (@lem7001814 B t _93317) (@lem7001798 A B t _93317 R _93316 _93318)). Qed.
Lemma lem7001826 {A : Type'} (s : A -> Prop) (_93316 : A) : (term964 A s _93316) = (term964 A s _93316).
Proof. exact (eq_refl (term964 A s _93316)). Qed.
Lemma lem7001827 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (_93317 : B) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1198 A B s _93317 t R _93316 _93318) = (term1199 A B s t _93317 R _93316 _93318).
Proof. exact (MK_COMB (@lem7001826 A s _93316) (@lem7001815 A B t _93317 R _93316 _93318)). Qed.
Lemma lem7001838 {B : Type'} (_93318 : B) (_93317 : B) : (term1200 B _93318 _93317) = (term1200 B _93318 _93317).
Proof. exact (eq_refl (term1200 B _93318 _93317)). Qed.
Lemma lem7001839 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (_93317 : B) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1201 A B s _93317 t R _93316 _93318) = (term1192 A B s t _93317 R _93316 _93318).
Proof. exact (MK_COMB (@lem7001838 B _93318 _93317) (@lem7001827 A B s t _93317 R _93316 _93318)). Qed.
Lemma lem7001850 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (_93317 : B) (R : type1413 A B) (_93316 : A) (_93318 : B) : ((term1138 A B s t R _93316 _93318 _93317) = (term1201 A B s _93317 t R _93316 _93318)) = ((term1192 A B s t _93317 R _93316 _93318) = (term1192 A B s t _93317 R _93316 _93318)).
Proof. exact (MK_COMB (@lem7001761 A B s t _93317 R _93316 _93318) (@lem7001839 A B s t _93317 R _93316 _93318)). Qed.
Lemma lem7001852 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7001853 (x : Prop) : (x = x) = True.
Proof. exact (@lem7001852 Prop x). Qed.
Lemma lem7001854 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (_93317 : B) (R : type1413 A B) (_93316 : A) (_93318 : B) : ((term1192 A B s t _93317 R _93316 _93318) = (term1192 A B s t _93317 R _93316 _93318)) = True.
Proof. exact (@lem7001853 (term1192 A B s t _93317 R _93316 _93318)). Qed.
Lemma lem7001855 {A B : Type'} (s : A -> Prop) (_93317 : B) (t : B -> Prop) (R : type1413 A B) (_93316 : A) (_93318 : B) : ((term1138 A B s t R _93316 _93318 _93317) = (term1201 A B s _93317 t R _93316 _93318)) = True.
Proof. exact (TRANS (@lem7001850 A B s t _93317 R _93316 _93318) (@lem7001854 A B s t _93317 R _93316 _93318)). Qed.
Lemma lem7001856 {A B : Type'} (s : A -> Prop) (_93317 : B) (t : B -> Prop) (R : type1413 A B) (_93316 : A) (_93318 : B) : True = ((term1138 A B s t R _93316 _93318 _93317) = (term1201 A B s _93317 t R _93316 _93318)).
Proof. exact (SYM (@lem7001855 A B s _93317 t R _93316 _93318)). Qed.
Lemma lem7001857 {A B : Type'} (s : A -> Prop) (_93317 : B) (t : B -> Prop) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1138 A B s t R _93316 _93318 _93317) = (term1201 A B s _93317 t R _93316 _93318).
Proof. exact (EQ_MP (@lem7001856 A B s _93317 t R _93316 _93318) (@lem0)). Qed.
Lemma lem7001858 {A B : Type'} (_93317 : B) (_93316 : A) (_93318 : B) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1201 A B s _93317 t R _93316 _93318.
Proof. exact (EQ_MP (@lem7001857 A B s _93317 t R _93316 _93318) (@lem7000524 A B _93316 _93318 _93317 x y t R s h1)). Qed.
Lemma lem7001860 (b : Prop) (a : Prop) : (a \/ b) = (term555 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7001861 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_93316 : A) (_93318 : B) (_93317 : B) : (term1201 A B s _93317 t R _93316 _93318) = (term1202 A B s t R _93316 _93318 _93317).
Proof. exact (@lem7001860 (term1198 A B s _93317 t R _93316 _93318) (_93318 = _93317)). Qed.
Lemma lem7001863 (a : Prop) (b : Prop) : (term582 a b) = (term583 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7001864 {A B : Type'} (s : A -> Prop) (_93317 : B) (t : B -> Prop) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1203 A B s _93317 t R _93316 _93318) = (term1204 A B s _93317 t R _93316 _93318).
Proof. exact (@lem7001863 (term963 A s _93316) (term1197 A B _93317 t R _93316 _93318)). Qed.
Lemma lem7001866 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7001867 {A : Type'} (s : A -> Prop) (_93316 : A) : (term1161 A s _93316) = (@I (A -> Prop) s _93316).
Proof. exact (@lem7001866 (@I (A -> Prop) s _93316)). Qed.
Lemma lem7001868 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7001869 {A : Type'} (s : A -> Prop) (_93316 : A) : (term1162 A s _93316) = (term977 A s _93316).
Proof. exact (MK_COMB (@lem7001868) (@lem7001867 A s _93316)). Qed.
Lemma lem7001871 (a : Prop) (b : Prop) : (term582 a b) = (term583 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7001872 {A B : Type'} (_93317 : B) (t : B -> Prop) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1205 A B _93317 t R _93316 _93318) = (term1206 A B _93317 t R _93316 _93318).
Proof. exact (@lem7001871 (term963 B t _93317) (term1196 A B _93317 t R _93316 _93318)). Qed.
Lemma lem7001874 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7001875 {B : Type'} (t : B -> Prop) (_93317 : B) : (term1161 B t _93317) = (@I (B -> Prop) t _93317).
Proof. exact (@lem7001874 (@I (B -> Prop) t _93317)). Qed.
Lemma lem7001876 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7001877 {B : Type'} (t : B -> Prop) (_93317 : B) : (term1162 B t _93317) = (term977 B t _93317).
Proof. exact (MK_COMB (@lem7001876) (@lem7001875 B t _93317)). Qed.
Lemma lem7001879 (a : Prop) (b : Prop) : (term582 a b) = (term583 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7001880 {A B : Type'} (_93317 : B) (t : B -> Prop) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1207 A B _93317 t R _93316 _93318) = (term1208 A B _93317 t R _93316 _93318).
Proof. exact (@lem7001879 (term380 A B R _93316 _93317) (term965 A B t R _93316 _93318)). Qed.
Lemma lem7001882 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7001883 {A B : Type'} (R : type1413 A B) (_93316 : A) (_93317 : B) : (term588 A B R _93316 _93317) = (term378 A B R _93316 _93317).
Proof. exact (@lem7001882 (term378 A B R _93316 _93317)). Qed.
Lemma lem7001884 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7001885 {A B : Type'} (R : type1413 A B) (_93316 : A) (_93317 : B) : (term1209 A B R _93316 _93317) = (term1210 A B R _93316 _93317).
Proof. exact (MK_COMB (@lem7001884) (@lem7001883 A B R _93316 _93317)). Qed.
Lemma lem7001887 (a : Prop) (b : Prop) : (term582 a b) = (term583 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7001888 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1159 A B t R _93316 _93318) = (term1160 A B t R _93316 _93318).
Proof. exact (@lem7001887 (term963 B t _93318) (term380 A B R _93316 _93318)). Qed.
Lemma lem7001890 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7001891 {B : Type'} (t : B -> Prop) (_93318 : B) : (term1161 B t _93318) = (@I (B -> Prop) t _93318).
Proof. exact (@lem7001890 (@I (B -> Prop) t _93318)). Qed.
Lemma lem7001892 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7001893 {B : Type'} (t : B -> Prop) (_93318 : B) : (term1162 B t _93318) = (term977 B t _93318).
Proof. exact (MK_COMB (@lem7001892) (@lem7001891 B t _93318)). Qed.
Lemma lem7001895 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7001896 {A B : Type'} (R : type1413 A B) (_93316 : A) (_93318 : B) : (term588 A B R _93316 _93318) = (term378 A B R _93316 _93318).
Proof. exact (@lem7001895 (term378 A B R _93316 _93318)). Qed.
Lemma lem7001897 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1160 A B t R _93316 _93318) = (term1163 A B t R _93316 _93318).
Proof. exact (MK_COMB (@lem7001893 B t _93318) (@lem7001896 A B R _93316 _93318)). Qed.
Lemma lem7001898 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1159 A B t R _93316 _93318) = (term1163 A B t R _93316 _93318).
Proof. exact (TRANS (@lem7001888 A B t R _93316 _93318) (@lem7001897 A B t R _93316 _93318)). Qed.
Lemma lem7001899 {A B : Type'} (_93317 : B) (t : B -> Prop) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1208 A B _93317 t R _93316 _93318) = (term1211 A B _93317 t R _93316 _93318).
Proof. exact (MK_COMB (@lem7001885 A B R _93316 _93317) (@lem7001898 A B t R _93316 _93318)). Qed.
Lemma lem7001900 {A B : Type'} (_93317 : B) (t : B -> Prop) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1207 A B _93317 t R _93316 _93318) = (term1211 A B _93317 t R _93316 _93318).
Proof. exact (TRANS (@lem7001880 A B _93317 t R _93316 _93318) (@lem7001899 A B _93317 t R _93316 _93318)). Qed.
Lemma lem7001901 {A B : Type'} (_93317 : B) (t : B -> Prop) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1206 A B _93317 t R _93316 _93318) = (term1212 A B _93317 t R _93316 _93318).
Proof. exact (MK_COMB (@lem7001877 B t _93317) (@lem7001900 A B _93317 t R _93316 _93318)). Qed.
Lemma lem7001902 {A B : Type'} (_93317 : B) (t : B -> Prop) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1205 A B _93317 t R _93316 _93318) = (term1212 A B _93317 t R _93316 _93318).
Proof. exact (TRANS (@lem7001872 A B _93317 t R _93316 _93318) (@lem7001901 A B _93317 t R _93316 _93318)). Qed.
Lemma lem7001903 {A B : Type'} (s : A -> Prop) (_93317 : B) (t : B -> Prop) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1204 A B s _93317 t R _93316 _93318) = (term1213 A B s _93317 t R _93316 _93318).
Proof. exact (MK_COMB (@lem7001869 A s _93316) (@lem7001902 A B _93317 t R _93316 _93318)). Qed.
Lemma lem7001904 {A B : Type'} (s : A -> Prop) (_93317 : B) (t : B -> Prop) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1203 A B s _93317 t R _93316 _93318) = (term1213 A B s _93317 t R _93316 _93318).
Proof. exact (TRANS (@lem7001864 A B s _93317 t R _93316 _93318) (@lem7001903 A B s _93317 t R _93316 _93318)). Qed.
Lemma lem7001905 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7001906 {A B : Type'} (s : A -> Prop) (_93317 : B) (t : B -> Prop) (R : type1413 A B) (_93316 : A) (_93318 : B) : (term1214 A B s _93317 t R _93316 _93318) = (term1215 A B s _93317 t R _93316 _93318).
Proof. exact (MK_COMB (@lem7001905) (@lem7001904 A B s _93317 t R _93316 _93318)). Qed.
Lemma lem7001907 {B : Type'} (_93318 : B) (_93317 : B) : (_93318 = _93317) = (_93318 = _93317).
Proof. exact (eq_refl (_93318 = _93317)). Qed.
Lemma lem7001908 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_93316 : A) (_93318 : B) (_93317 : B) : (term1202 A B s t R _93316 _93318 _93317) = (term1216 A B s t R _93316 _93318 _93317).
Proof. exact (MK_COMB (@lem7001906 A B s _93317 t R _93316 _93318) (@lem7001907 B _93318 _93317)). Qed.
Lemma lem7001909 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (_93316 : A) (_93318 : B) (_93317 : B) : (term1201 A B s _93317 t R _93316 _93318) = (term1216 A B s t R _93316 _93318 _93317).
Proof. exact (TRANS (@lem7001861 A B s t R _93316 _93318 _93317) (@lem7001908 A B s t R _93316 _93318 _93317)). Qed.
Lemma lem7001911 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term940 A B x y t R s) (h3 : term987 A B s _93304 t R x' x) : term962 A B _93304 t R x'.
Proof. exact (conj (@lem7001418 A B y s _93304 t R x' x h1 h2 h3) (@lem7001539 A B y s _93304 t R x' x h1 h2 h3)). Qed.
Lemma lem7001912 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term940 A B x y t R s) (h3 : term987 A B s _93304 t R x' x) : term1217 A B x _93304 t R x'.
Proof. exact (conj (@lem7001297 A B s _93304 t R x' x h3) (@lem7001911 A B y s _93304 t R x' x h1 h2 h3)). Qed.
Lemma lem7001913 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term940 A B x y t R s) (h3 : term987 A B s _93304 t R x' x) : term1218 A B x _93304 t R x'.
Proof. exact (conj (@lem7001290 A B x y t R s h2) (@lem7001912 A B y s _93304 t R x' x h1 h2 h3)). Qed.
Lemma lem7001914 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term940 A B x y t R s) (h3 : term987 A B s _93304 t R x' x) : term1219 A B s x _93304 t R x'.
Proof. exact (conj (@lem7001283 A B s _93304 t R x' x h3) (@lem7001913 A B y s _93304 t R x' x h1 h2 h3)). Qed.
Lemma lem7001916 {A B : Type'} (_93316 : A) (_93318 : B) (_93317 : B) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1216 A B s t R _93316 _93318 _93317.
Proof. exact (EQ_MP (@lem7001909 A B s t R _93316 _93318 _93317) (@lem7001858 A B _93317 _93316 _93318 x y t R s h1)). Qed.
Lemma lem7001917 {A B : Type'} (_93316 : A) (_93318 : B) (_93317 : B) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1216 A B s t R _93316 _93318 _93317.
Proof. exact (@lem7001916 A B _93316 _93318 _93317 x y t R s h1). Qed.
Lemma lem7001918 {A B : Type'} (_93304 : type830 A B) (x' : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1220 A B s _93304 t R x' x.
Proof. exact (@lem7001917 A B x' (term367 A B _93304 t R x') x x y t R s h1). Qed.
Lemma lem7001921 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term940 A B x y t R s) (h3 : term987 A B s _93304 t R x' x) : (term367 A B _93304 t R x') = x.
Proof. exact (@lem7001918 A B _93304 x' x y t R s h2 (@lem7001914 A B y s _93304 t R x' x h1 h2 h3)). Qed.
Lemma lem7001922 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term940 A B x y t R s) (h3 : term987 A B s _93304 t R x' x) : term1221 A B _93304 t R x' x.
Proof. exact (fun h0 : term983 A B _93304 t R x' x => @lem7001921 A B y s _93304 t R x' x h1 h2 h3). Qed.
Lemma lem7001924 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7001925 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term1221 A B _93304 t R x' x) = ((term367 A B _93304 t R x') = x).
Proof. exact (@lem7001924 ((term367 A B _93304 t R x') = x)). Qed.
Lemma lem7001926 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term940 A B x y t R s) (h3 : term987 A B s _93304 t R x' x) : (term367 A B _93304 t R x') = x.
Proof. exact (EQ_MP (@lem7001925 A B _93304 t R x' x) (@lem7001922 A B y s _93304 t R x' x h1 h2 h3)). Qed.
Lemma lem7001929 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7001931 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) : (term983 A B _93304 t R x' x) = (term1222 A B _93304 t R x' x).
Proof. exact (@lem7001929 ((term367 A B _93304 t R x') = x)). Qed.
Lemma lem7001934 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term983 A B _93304 t R x' x) : term1222 A B _93304 t R x' x.
Proof. exact (EQ_MP (@lem7001931 A B _93304 t R x' x) (@lem7000498 A B _93304 t R x' x h1)). Qed.
Lemma lem7001937 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term983 A B _93304 t R x' x) (h3 : term940 A B x y t R s) (h4 : term987 A B s _93304 t R x' x) : False.
Proof. exact (@lem7001934 A B _93304 t R x' x h2 (@lem7001926 A B y s _93304 t R x' x h1 h3 h4)). Qed.
Lemma lem7001938 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term983 A B _93304 t R x' x) (h3 : term940 A B x y t R s) (h4 : term987 A B s _93304 t R x' x) : term596.
Proof. exact (fun h0 : ~ False => @lem7001937 A B y s _93304 t R x' x h1 h2 h3 h4). Qed.
Lemma lem7001940 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7001941 : term596 = False.
Proof. exact (@lem7001940 False). Qed.
Lemma lem7001942 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term983 A B _93304 t R x' x) (h3 : term940 A B x y t R s) (h4 : term987 A B s _93304 t R x' x) : False.
Proof. exact (EQ_MP (@lem7001941) (@lem7001938 A B y s _93304 t R x' x h1 h2 h3 h4)). Qed.
Lemma lem7002079 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _93304 t R x' x) : @I (A -> Prop) s x'.
Proof. exact (proj1 (@lem6999215 A B s _93304 t R x' x h1)). Qed.
Lemma lem7002080 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _93304 t R x' x) : term1149 A s x'.
Proof. exact (fun h0 : term963 A s x' => @lem7002079 A B s _93304 t R x' x h1). Qed.
Lemma lem7002082 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7002083 {A : Type'} (s : A -> Prop) (x' : A) : (term1149 A s x') = (@I (A -> Prop) s x').
Proof. exact (@lem7002082 (@I (A -> Prop) s x')). Qed.
Lemma lem7002084 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _93304 t R x' x) : @I (A -> Prop) s x'.
Proof. exact (EQ_MP (@lem7002083 A s x') (@lem7002080 A B s _93304 t R x' x h1)). Qed.
Lemma lem7002087 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7002089 {A : Type'} (s : A -> Prop) (x' : A) : (term963 A s x') = (term1150 A s x').
Proof. exact (@lem7002087 (@I (A -> Prop) s x')). Qed.
Lemma lem7002092 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term963 A s x') : term1150 A s x'.
Proof. exact (EQ_MP (@lem7002089 A s x') (@lem7000774 A s x' h1)). Qed.
Lemma lem7002095 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term981 A B s _93304 t R x' x) : False.
Proof. exact (@lem7002092 A s x' h1 (@lem7002084 A B s _93304 t R x' x h2)). Qed.
Lemma lem7002096 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term981 A B s _93304 t R x' x) : term596.
Proof. exact (fun h0 : ~ False => @lem7002095 A B s _93304 t R x' x h1 h2). Qed.
Lemma lem7002098 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7002099 : term596 = False.
Proof. exact (@lem7002098 False). Qed.
Lemma lem7002100 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term981 A B s _93304 t R x' x) : False.
Proof. exact (EQ_MP (@lem7002099) (@lem7002096 A B s _93304 t R x' x h1 h2)). Qed.
Lemma lem7002237 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _93304 t R x' x) : @I (A -> Prop) s x'.
Proof. exact (proj1 (@lem6999215 A B s _93304 t R x' x h1)). Qed.
Lemma lem7002238 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _93304 t R x' x) : term1149 A s x'.
Proof. exact (fun h0 : term963 A s x' => @lem7002237 A B s _93304 t R x' x h1). Qed.
Lemma lem7002240 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7002241 {A : Type'} (s : A -> Prop) (x' : A) : (term1149 A s x') = (@I (A -> Prop) s x').
Proof. exact (@lem7002240 (@I (A -> Prop) s x')). Qed.
Lemma lem7002242 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _93304 t R x' x) : @I (A -> Prop) s x'.
Proof. exact (EQ_MP (@lem7002241 A s x') (@lem7002238 A B s _93304 t R x' x h1)). Qed.
Lemma lem7002248 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7002249 {A B : Type'} (t : B -> Prop) (y : A -> B) (s : A -> Prop) (_93330 : A) : (term1147 A B s t y _93330) = (term1223 A B t y s _93330).
Proof. exact (@lem7002248 (term999 A B t y _93330) (term963 A s _93330)). Qed.
Lemma lem7002255 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7002256 {A B : Type'} (t : B -> Prop) (y : A -> B) (s : A -> Prop) (_93330 : A) : (term1224 A B s t y _93330) = (term1225 A B t y s _93330).
Proof. exact (MK_COMB (@lem7002255) (@lem7002249 A B t y s _93330)). Qed.
Lemma lem7002262 {A B : Type'} (t : B -> Prop) (y : A -> B) (s : A -> Prop) (_93330 : A) : (term1223 A B t y s _93330) = (term1223 A B t y s _93330).
Proof. exact (eq_refl (term1223 A B t y s _93330)). Qed.
Lemma lem7002263 {A B : Type'} (t : B -> Prop) (y : A -> B) (s : A -> Prop) (_93330 : A) : ((term1147 A B s t y _93330) = (term1223 A B t y s _93330)) = ((term1223 A B t y s _93330) = (term1223 A B t y s _93330)).
Proof. exact (MK_COMB (@lem7002256 A B t y s _93330) (@lem7002262 A B t y s _93330)). Qed.
Lemma lem7002265 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7002266 (x : Prop) : (x = x) = True.
Proof. exact (@lem7002265 Prop x). Qed.
Lemma lem7002267 {A B : Type'} (t : B -> Prop) (y : A -> B) (s : A -> Prop) (_93330 : A) : ((term1223 A B t y s _93330) = (term1223 A B t y s _93330)) = True.
Proof. exact (@lem7002266 (term1223 A B t y s _93330)). Qed.
Lemma lem7002268 {A B : Type'} (t : B -> Prop) (y : A -> B) (s : A -> Prop) (_93330 : A) : ((term1147 A B s t y _93330) = (term1223 A B t y s _93330)) = True.
Proof. exact (TRANS (@lem7002263 A B t y s _93330) (@lem7002267 A B t y s _93330)). Qed.
Lemma lem7002269 {A B : Type'} (t : B -> Prop) (y : A -> B) (s : A -> Prop) (_93330 : A) : True = ((term1147 A B s t y _93330) = (term1223 A B t y s _93330)).
Proof. exact (SYM (@lem7002268 A B t y s _93330)). Qed.
Lemma lem7002270 {A B : Type'} (t : B -> Prop) (y : A -> B) (s : A -> Prop) (_93330 : A) : (term1147 A B s t y _93330) = (term1223 A B t y s _93330).
Proof. exact (EQ_MP (@lem7002269 A B t y s _93330) (@lem0)). Qed.
Lemma lem7002271 {A B : Type'} (_93330 : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1223 A B t y s _93330.
Proof. exact (EQ_MP (@lem7002270 A B t y s _93330) (@lem7000941 A B _93330 x y t R s h1)). Qed.
Lemma lem7002273 (b : Prop) (a : Prop) : (a \/ b) = (term555 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7002274 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (y : A -> B) (_93330 : A) : (term1223 A B t y s _93330) = (term1226 A B s t y _93330).
Proof. exact (@lem7002273 (term963 A s _93330) (term999 A B t y _93330)). Qed.
Lemma lem7002276 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7002277 {A : Type'} (s : A -> Prop) (_93330 : A) : (term1161 A s _93330) = (@I (A -> Prop) s _93330).
Proof. exact (@lem7002276 (@I (A -> Prop) s _93330)). Qed.
Lemma lem7002278 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7002279 {A : Type'} (s : A -> Prop) (_93330 : A) : (term1227 A s _93330) = (term1228 A s _93330).
Proof. exact (MK_COMB (@lem7002278) (@lem7002277 A s _93330)). Qed.
Lemma lem7002280 {A B : Type'} (t : B -> Prop) (y : A -> B) (_93330 : A) : (term999 A B t y _93330) = (term999 A B t y _93330).
Proof. exact (eq_refl (term999 A B t y _93330)). Qed.
Lemma lem7002281 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (y : A -> B) (_93330 : A) : (term1226 A B s t y _93330) = (term1229 A B s t y _93330).
Proof. exact (MK_COMB (@lem7002279 A s _93330) (@lem7002280 A B t y _93330)). Qed.
Lemma lem7002282 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (y : A -> B) (_93330 : A) : (term1223 A B t y s _93330) = (term1229 A B s t y _93330).
Proof. exact (TRANS (@lem7002274 A B s t y _93330) (@lem7002281 A B s t y _93330)). Qed.
Lemma lem7002285 {A B : Type'} (_93330 : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1229 A B s t y _93330.
Proof. exact (EQ_MP (@lem7002282 A B s t y _93330) (@lem7002271 A B _93330 x y t R s h1)). Qed.
Lemma lem7002286 {A B : Type'} (_93330 : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1229 A B s t y _93330.
Proof. exact (@lem7002285 A B _93330 x y t R s h1). Qed.
Lemma lem7002287 {A B : Type'} (x' : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1229 A B s t y x'.
Proof. exact (@lem7002286 A B x' x y t R s h1). Qed.
Lemma lem7002290 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term940 A B x y t R s) (h2 : term981 A B s _93304 t R x' x) : term999 A B t y x'.
Proof. exact (@lem7002287 A B x' x y t R s h1 (@lem7002242 A B s _93304 t R x' x h2)). Qed.
Lemma lem7002291 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term940 A B x y t R s) (h2 : term981 A B s _93304 t R x' x) : term1230 A B t y x'.
Proof. exact (fun h0 : term1231 A B t y x' => @lem7002290 A B y s _93304 t R x' x h1 h2). Qed.
Lemma lem7002293 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7002294 {A B : Type'} (t : B -> Prop) (y : A -> B) (x' : A) : (term1230 A B t y x') = (term999 A B t y x').
Proof. exact (@lem7002293 (term999 A B t y x')). Qed.
Lemma lem7002295 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term940 A B x y t R s) (h2 : term981 A B s _93304 t R x' x) : term999 A B t y x'.
Proof. exact (EQ_MP (@lem7002294 A B t y x') (@lem7002291 A B y s _93304 t R x' x h1 h2)). Qed.
Lemma lem7002297 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _93304 t R x' x) : @I (A -> Prop) s x'.
Proof. exact (proj1 (@lem6999215 A B s _93304 t R x' x h1)). Qed.
Lemma lem7002298 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _93304 t R x' x) : term1149 A s x'.
Proof. exact (fun h0 : term963 A s x' => @lem7002297 A B s _93304 t R x' x h1). Qed.
Lemma lem7002300 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7002301 {A : Type'} (s : A -> Prop) (x' : A) : (term1149 A s x') = (@I (A -> Prop) s x').
Proof. exact (@lem7002300 (@I (A -> Prop) s x')). Qed.
Lemma lem7002302 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term981 A B s _93304 t R x' x) : @I (A -> Prop) s x'.
Proof. exact (EQ_MP (@lem7002301 A s x') (@lem7002298 A B s _93304 t R x' x h1)). Qed.
Lemma lem7002308 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7002309 {A B : Type'} (R : type1413 A B) (y : A -> B) (s : A -> Prop) (_93330 : A) : (term1148 A B s R y _93330) = (term1232 A B R y s _93330).
Proof. exact (@lem7002308 (term406 A B R y _93330) (term963 A s _93330)). Qed.
Lemma lem7002315 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7002316 {A B : Type'} (R : type1413 A B) (y : A -> B) (s : A -> Prop) (_93330 : A) : (term1233 A B s R y _93330) = (term1234 A B R y s _93330).
Proof. exact (MK_COMB (@lem7002315) (@lem7002309 A B R y s _93330)). Qed.
Lemma lem7002322 {A B : Type'} (R : type1413 A B) (y : A -> B) (s : A -> Prop) (_93330 : A) : (term1232 A B R y s _93330) = (term1232 A B R y s _93330).
Proof. exact (eq_refl (term1232 A B R y s _93330)). Qed.
Lemma lem7002323 {A B : Type'} (R : type1413 A B) (y : A -> B) (s : A -> Prop) (_93330 : A) : ((term1148 A B s R y _93330) = (term1232 A B R y s _93330)) = ((term1232 A B R y s _93330) = (term1232 A B R y s _93330)).
Proof. exact (MK_COMB (@lem7002316 A B R y s _93330) (@lem7002322 A B R y s _93330)). Qed.
Lemma lem7002325 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7002326 (x : Prop) : (x = x) = True.
Proof. exact (@lem7002325 Prop x). Qed.
Lemma lem7002327 {A B : Type'} (R : type1413 A B) (y : A -> B) (s : A -> Prop) (_93330 : A) : ((term1232 A B R y s _93330) = (term1232 A B R y s _93330)) = True.
Proof. exact (@lem7002326 (term1232 A B R y s _93330)). Qed.
Lemma lem7002328 {A B : Type'} (R : type1413 A B) (y : A -> B) (s : A -> Prop) (_93330 : A) : ((term1148 A B s R y _93330) = (term1232 A B R y s _93330)) = True.
Proof. exact (TRANS (@lem7002323 A B R y s _93330) (@lem7002327 A B R y s _93330)). Qed.
Lemma lem7002329 {A B : Type'} (R : type1413 A B) (y : A -> B) (s : A -> Prop) (_93330 : A) : True = ((term1148 A B s R y _93330) = (term1232 A B R y s _93330)).
Proof. exact (SYM (@lem7002328 A B R y s _93330)). Qed.
Lemma lem7002330 {A B : Type'} (R : type1413 A B) (y : A -> B) (s : A -> Prop) (_93330 : A) : (term1148 A B s R y _93330) = (term1232 A B R y s _93330).
Proof. exact (EQ_MP (@lem7002329 A B R y s _93330) (@lem0)). Qed.
Lemma lem7002331 {A B : Type'} (_93330 : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1232 A B R y s _93330.
Proof. exact (EQ_MP (@lem7002330 A B R y s _93330) (@lem7000955 A B _93330 x y t R s h1)). Qed.
Lemma lem7002333 (b : Prop) (a : Prop) : (a \/ b) = (term555 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7002334 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (y : A -> B) (_93330 : A) : (term1232 A B R y s _93330) = (term1235 A B s R y _93330).
Proof. exact (@lem7002333 (term963 A s _93330) (term406 A B R y _93330)). Qed.
Lemma lem7002336 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7002337 {A : Type'} (s : A -> Prop) (_93330 : A) : (term1161 A s _93330) = (@I (A -> Prop) s _93330).
Proof. exact (@lem7002336 (@I (A -> Prop) s _93330)). Qed.
Lemma lem7002338 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7002339 {A : Type'} (s : A -> Prop) (_93330 : A) : (term1227 A s _93330) = (term1228 A s _93330).
Proof. exact (MK_COMB (@lem7002338) (@lem7002337 A s _93330)). Qed.
Lemma lem7002340 {A B : Type'} (R : type1413 A B) (y : A -> B) (_93330 : A) : (term406 A B R y _93330) = (term406 A B R y _93330).
Proof. exact (eq_refl (term406 A B R y _93330)). Qed.
Lemma lem7002341 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (y : A -> B) (_93330 : A) : (term1235 A B s R y _93330) = (term1236 A B s R y _93330).
Proof. exact (MK_COMB (@lem7002339 A s _93330) (@lem7002340 A B R y _93330)). Qed.
Lemma lem7002342 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (y : A -> B) (_93330 : A) : (term1232 A B R y s _93330) = (term1236 A B s R y _93330).
Proof. exact (TRANS (@lem7002334 A B s R y _93330) (@lem7002341 A B s R y _93330)). Qed.
Lemma lem7002345 {A B : Type'} (_93330 : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1236 A B s R y _93330.
Proof. exact (EQ_MP (@lem7002342 A B s R y _93330) (@lem7002331 A B _93330 x y t R s h1)). Qed.
Lemma lem7002346 {A B : Type'} (_93330 : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1236 A B s R y _93330.
Proof. exact (@lem7002345 A B _93330 x y t R s h1). Qed.
Lemma lem7002347 {A B : Type'} (x' : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term940 A B x y t R s) : term1236 A B s R y x'.
Proof. exact (@lem7002346 A B x' x y t R s h1). Qed.
Lemma lem7002350 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term940 A B x y t R s) (h2 : term981 A B s _93304 t R x' x) : term406 A B R y x'.
Proof. exact (@lem7002347 A B x' x y t R s h1 (@lem7002302 A B s _93304 t R x' x h2)). Qed.
Lemma lem7002351 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term940 A B x y t R s) (h2 : term981 A B s _93304 t R x' x) : term568 A B R y x'.
Proof. exact (fun h0 : term569 A B R y x' => @lem7002350 A B y s _93304 t R x' x h1 h2). Qed.
Lemma lem7002353 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7002354 {A B : Type'} (R : type1413 A B) (y : A -> B) (x' : A) : (term568 A B R y x') = (term406 A B R y x').
Proof. exact (@lem7002353 (term406 A B R y x')). Qed.
Lemma lem7002355 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term940 A B x y t R s) (h2 : term981 A B s _93304 t R x' x) : term406 A B R y x'.
Proof. exact (EQ_MP (@lem7002354 A B R y x') (@lem7002351 A B y s _93304 t R x' x h1 h2)). Qed.
Lemma lem7002371 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7002372 {A B : Type'} (_93304 : type830 A B) (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) (_93329 : B) : (term1169 A B _93329 _93304 _93326 _93327 _93328) = (term1170 A B _93304 _93326 _93327 _93328 _93329).
Proof. exact (@lem7002371 (term370 A B _93304 _93326 _93327 _93328) (term380 A B _93327 _93328 _93329)). Qed.
Lemma lem7002378 {B : Type'} (_93326 : B -> Prop) (_93329 : B) : (term964 B _93326 _93329) = (term964 B _93326 _93329).
Proof. exact (eq_refl (term964 B _93326 _93329)). Qed.
Lemma lem7002379 {A B : Type'} (_93304 : type830 A B) (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) (_93329 : B) : (term1140 A B _93329 _93304 _93326 _93327 _93328) = (term1171 A B _93304 _93326 _93327 _93328 _93329).
Proof. exact (MK_COMB (@lem7002378 B _93326 _93329) (@lem7002372 A B _93304 _93326 _93327 _93328 _93329)). Qed.
Lemma lem7002383 (q : Prop) (p : Prop) (r : Prop) : (term21 p q r) = (term21 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7002384 {A B : Type'} (_93304 : type830 A B) (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) (_93329 : B) : (term1171 A B _93304 _93326 _93327 _93328 _93329) = (term1172 A B _93304 _93326 _93327 _93328 _93329).
Proof. exact (@lem7002383 (term370 A B _93304 _93326 _93327 _93328) (term963 B _93326 _93329) (term380 A B _93327 _93328 _93329)). Qed.
Lemma lem7002400 {A B : Type'} (_93304 : type830 A B) (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) (_93329 : B) : (term1140 A B _93329 _93304 _93326 _93327 _93328) = (term1172 A B _93304 _93326 _93327 _93328 _93329).
Proof. exact (TRANS (@lem7002379 A B _93304 _93326 _93327 _93328 _93329) (@lem7002384 A B _93304 _93326 _93327 _93328 _93329)). Qed.
Lemma lem7002401 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7002402 {A B : Type'} (_93304 : type830 A B) (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) (_93329 : B) : (term1173 A B _93329 _93304 _93326 _93327 _93328) = (term1174 A B _93304 _93326 _93327 _93328 _93329).
Proof. exact (MK_COMB (@lem7002401) (@lem7002400 A B _93304 _93326 _93327 _93328 _93329)). Qed.
Lemma lem7002418 {A B : Type'} (_93304 : type830 A B) (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) (_93329 : B) : (term1172 A B _93304 _93326 _93327 _93328 _93329) = (term1172 A B _93304 _93326 _93327 _93328 _93329).
Proof. exact (eq_refl (term1172 A B _93304 _93326 _93327 _93328 _93329)). Qed.
Lemma lem7002419 {A B : Type'} (_93304 : type830 A B) (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) (_93329 : B) : ((term1140 A B _93329 _93304 _93326 _93327 _93328) = (term1172 A B _93304 _93326 _93327 _93328 _93329)) = ((term1172 A B _93304 _93326 _93327 _93328 _93329) = (term1172 A B _93304 _93326 _93327 _93328 _93329)).
Proof. exact (MK_COMB (@lem7002402 A B _93304 _93326 _93327 _93328 _93329) (@lem7002418 A B _93304 _93326 _93327 _93328 _93329)). Qed.
Lemma lem7002421 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7002422 (x : Prop) : (x = x) = True.
Proof. exact (@lem7002421 Prop x). Qed.
Lemma lem7002423 {A B : Type'} (_93304 : type830 A B) (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) (_93329 : B) : ((term1172 A B _93304 _93326 _93327 _93328 _93329) = (term1172 A B _93304 _93326 _93327 _93328 _93329)) = True.
Proof. exact (@lem7002422 (term1172 A B _93304 _93326 _93327 _93328 _93329)). Qed.
Lemma lem7002424 {A B : Type'} (_93304 : type830 A B) (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) (_93329 : B) : ((term1140 A B _93329 _93304 _93326 _93327 _93328) = (term1172 A B _93304 _93326 _93327 _93328 _93329)) = True.
Proof. exact (TRANS (@lem7002419 A B _93304 _93326 _93327 _93328 _93329) (@lem7002423 A B _93304 _93326 _93327 _93328 _93329)). Qed.
Lemma lem7002425 {A B : Type'} (_93304 : type830 A B) (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) (_93329 : B) : True = ((term1140 A B _93329 _93304 _93326 _93327 _93328) = (term1172 A B _93304 _93326 _93327 _93328 _93329)).
Proof. exact (SYM (@lem7002424 A B _93304 _93326 _93327 _93328 _93329)). Qed.
Lemma lem7002426 {A B : Type'} (_93304 : type830 A B) (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) (_93329 : B) : (term1140 A B _93329 _93304 _93326 _93327 _93328) = (term1172 A B _93304 _93326 _93327 _93328 _93329).
Proof. exact (EQ_MP (@lem7002425 A B _93304 _93326 _93327 _93328 _93329) (@lem0)). Qed.
Lemma lem7002427 {A B : Type'} (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) (_93329 : B) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1172 A B _93304 _93326 _93327 _93328 _93329.
Proof. exact (EQ_MP (@lem7002426 A B _93304 _93326 _93327 _93328 _93329) (@lem7000983 A B _93329 _93326 _93327 _93328 _93304 h1)). Qed.
Lemma lem7002429 (b : Prop) (a : Prop) : (a \/ b) = (term555 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7002430 {A B : Type'} (_93329 : B) (_93304 : type830 A B) (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) : (term1172 A B _93304 _93326 _93327 _93328 _93329) = (term1175 A B _93329 _93304 _93326 _93327 _93328).
Proof. exact (@lem7002429 (term965 A B _93326 _93327 _93328 _93329) (term370 A B _93304 _93326 _93327 _93328)). Qed.
Lemma lem7002432 (a : Prop) (b : Prop) : (term582 a b) = (term583 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7002433 {A B : Type'} (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) (_93329 : B) : (term1159 A B _93326 _93327 _93328 _93329) = (term1160 A B _93326 _93327 _93328 _93329).
Proof. exact (@lem7002432 (term963 B _93326 _93329) (term380 A B _93327 _93328 _93329)). Qed.
Lemma lem7002435 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7002436 {B : Type'} (_93326 : B -> Prop) (_93329 : B) : (term1161 B _93326 _93329) = (@I (B -> Prop) _93326 _93329).
Proof. exact (@lem7002435 (@I (B -> Prop) _93326 _93329)). Qed.
Lemma lem7002437 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7002438 {B : Type'} (_93326 : B -> Prop) (_93329 : B) : (term1162 B _93326 _93329) = (term977 B _93326 _93329).
Proof. exact (MK_COMB (@lem7002437) (@lem7002436 B _93326 _93329)). Qed.
Lemma lem7002440 (a : Prop) : (term203 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7002441 {A B : Type'} (_93327 : type1413 A B) (_93328 : A) (_93329 : B) : (term588 A B _93327 _93328 _93329) = (term378 A B _93327 _93328 _93329).
Proof. exact (@lem7002440 (term378 A B _93327 _93328 _93329)). Qed.
Lemma lem7002442 {A B : Type'} (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) (_93329 : B) : (term1160 A B _93326 _93327 _93328 _93329) = (term1163 A B _93326 _93327 _93328 _93329).
Proof. exact (MK_COMB (@lem7002438 B _93326 _93329) (@lem7002441 A B _93327 _93328 _93329)). Qed.
Lemma lem7002443 {A B : Type'} (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) (_93329 : B) : (term1159 A B _93326 _93327 _93328 _93329) = (term1163 A B _93326 _93327 _93328 _93329).
Proof. exact (TRANS (@lem7002433 A B _93326 _93327 _93328 _93329) (@lem7002442 A B _93326 _93327 _93328 _93329)). Qed.
Lemma lem7002444 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7002445 {A B : Type'} (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) (_93329 : B) : (term1164 A B _93326 _93327 _93328 _93329) = (term1165 A B _93326 _93327 _93328 _93329).
Proof. exact (MK_COMB (@lem7002444) (@lem7002443 A B _93326 _93327 _93328 _93329)). Qed.
Lemma lem7002446 {A B : Type'} (_93304 : type830 A B) (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) : (term370 A B _93304 _93326 _93327 _93328) = (term370 A B _93304 _93326 _93327 _93328).
Proof. exact (eq_refl (term370 A B _93304 _93326 _93327 _93328)). Qed.
Lemma lem7002447 {A B : Type'} (_93329 : B) (_93304 : type830 A B) (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) : (term1175 A B _93329 _93304 _93326 _93327 _93328) = (term1176 A B _93329 _93304 _93326 _93327 _93328).
Proof. exact (MK_COMB (@lem7002445 A B _93326 _93327 _93328 _93329) (@lem7002446 A B _93304 _93326 _93327 _93328)). Qed.
Lemma lem7002448 {A B : Type'} (_93329 : B) (_93304 : type830 A B) (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) : (term1172 A B _93304 _93326 _93327 _93328 _93329) = (term1176 A B _93329 _93304 _93326 _93327 _93328).
Proof. exact (TRANS (@lem7002430 A B _93329 _93304 _93326 _93327 _93328) (@lem7002447 A B _93329 _93304 _93326 _93327 _93328)). Qed.
Lemma lem7002450 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term940 A B x y t R s) (h2 : term981 A B s _93304 t R x' x) : term1003 A B t R y x'.
Proof. exact (conj (@lem7002295 A B y s _93304 t R x' x h1 h2) (@lem7002355 A B y s _93304 t R x' x h1 h2)). Qed.
Lemma lem7002452 {A B : Type'} (_93329 : B) (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1176 A B _93329 _93304 _93326 _93327 _93328.
Proof. exact (EQ_MP (@lem7002448 A B _93329 _93304 _93326 _93327 _93328) (@lem7002427 A B _93326 _93327 _93328 _93329 _93304 h1)). Qed.
Lemma lem7002453 {A B : Type'} (_93329 : B) (_93326 : B -> Prop) (_93327 : type1413 A B) (_93328 : A) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1176 A B _93329 _93304 _93326 _93327 _93328.
Proof. exact (@lem7002452 A B _93329 _93326 _93327 _93328 _93304 h1). Qed.
Lemma lem7002454 {A B : Type'} (y : A -> B) (t : B -> Prop) (R : type1413 A B) (x' : A) (_93304 : type830 A B) (h1 : term728 A B _93304) : term1237 A B y _93304 t R x'.
Proof. exact (@lem7002453 A B (@I (A -> B) y x') t R x' _93304 h1). Qed.
Lemma lem7002457 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term940 A B x y t R s) (h3 : term981 A B s _93304 t R x' x) : term370 A B _93304 t R x'.
Proof. exact (@lem7002454 A B y t R x' _93304 h1 (@lem7002450 A B y s _93304 t R x' x h2 h3)). Qed.
Lemma lem7002458 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term940 A B x y t R s) (h3 : term981 A B s _93304 t R x' x) : term1177 A B _93304 t R x'.
Proof. exact (fun h0 : term1144 A B _93304 t R x' => @lem7002457 A B y s _93304 t R x' x h1 h2 h3). Qed.
Lemma lem7002460 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7002461 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term1177 A B _93304 t R x') = (term370 A B _93304 t R x').
Proof. exact (@lem7002460 (term370 A B _93304 t R x')). Qed.
Lemma lem7002462 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term940 A B x y t R s) (h3 : term981 A B s _93304 t R x' x) : term370 A B _93304 t R x'.
Proof. exact (EQ_MP (@lem7002461 A B _93304 t R x') (@lem7002458 A B y s _93304 t R x' x h1 h2 h3)). Qed.
Lemma lem7002465 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7002467 {A B : Type'} (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) : (term1144 A B _93304 t R x') = (term1238 A B _93304 t R x').
Proof. exact (@lem7002465 (term370 A B _93304 t R x')). Qed.
Lemma lem7002470 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term380 A B R x' x) (h2 : term981 A B s _93304 t R x' x) : term1238 A B _93304 t R x'.
Proof. exact (EQ_MP (@lem7002467 A B _93304 t R x') (@lem7000913 A B s _93304 t R x' x h1 h2)). Qed.
Lemma lem7002473 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term380 A B R x' x) (h3 : term940 A B x y t R s) (h4 : term981 A B s _93304 t R x' x) : False.
Proof. exact (@lem7002470 A B s _93304 t R x' x h2 h4 (@lem7002462 A B y s _93304 t R x' x h1 h3 h4)). Qed.
Lemma lem7002474 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term380 A B R x' x) (h3 : term940 A B x y t R s) (h4 : term981 A B s _93304 t R x' x) : term596.
Proof. exact (fun h0 : ~ False => @lem7002473 A B y s _93304 t R x' x h1 h2 h3 h4). Qed.
Lemma lem7002476 (p : Prop) : (term551 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7002477 : term596 = False.
Proof. exact (@lem7002476 False). Qed.
Lemma lem7002479 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term380 A B R x' x) (h3 : term940 A B x y t R s) (h4 : term981 A B s _93304 t R x' x) : False.
Proof. exact (EQ_MP (@lem7002477) (@lem7002474 A B y s _93304 t R x' x h1 h2 h3 h4)). Qed.
Lemma lem7002480 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term981 A B s _93304 t R x' x) : (term963 A s x') = False.
Proof. exact (prop_ext (fun h3 : term963 A s x' => @lem7002100 A B s _93304 t R x' x h1 h2) (fun h3 : False => @lem7000774 A s x' h1)). Qed.
Lemma lem7002482 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term981 A B s _93304 t R x' x) : False.
Proof. exact (EQ_MP (@lem7002480 A B s _93304 t R x' x h1 h2) (@lem7000774 A s x' h1)). Qed.
Lemma lem7002483 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term380 A B R x' x) (h3 : term940 A B x y t R s) (h4 : term981 A B s _93304 t R x' x) : (term380 A B R x' x) = False.
Proof. exact (prop_ext (fun h5 : term380 A B R x' x => @lem7002479 A B y s _93304 t R x' x h1 h2 h3 h4) (fun h5 : False => @lem7000642 A B R x' x h2)). Qed.
Lemma lem7002484 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term380 A B R x' x) (h3 : term940 A B x y t R s) (h4 : term981 A B s _93304 t R x' x) : False.
Proof. exact (EQ_MP (@lem7002483 A B y s _93304 t R x' x h1 h2 h3 h4) (@lem7000642 A B R x' x h2)). Qed.
Lemma lem7002485 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term981 A B s _93304 t R x' x) : (term963 A s x') = False.
Proof. exact (prop_ext (fun h3 : term963 A s x' => @lem7002482 A B s _93304 t R x' x h1 h2) (fun h3 : False => @lem7000570 A s x' h1)). Qed.
Lemma lem7002486 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term981 A B s _93304 t R x' x) : False.
Proof. exact (EQ_MP (@lem7002485 A B s _93304 t R x' x h1 h2) (@lem7000570 A s x' h1)). Qed.
Lemma lem7002487 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term983 A B _93304 t R x' x) (h3 : term940 A B x y t R s) (h4 : term987 A B s _93304 t R x' x) : (term983 A B _93304 t R x' x) = False.
Proof. exact (prop_ext (fun h5 : term983 A B _93304 t R x' x => @lem7001942 A B y s _93304 t R x' x h1 h2 h3 h4) (fun h5 : False => @lem7000498 A B _93304 t R x' x h2)). Qed.
Lemma lem7002488 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term983 A B _93304 t R x' x) (h3 : term940 A B x y t R s) (h4 : term987 A B s _93304 t R x' x) : False.
Proof. exact (EQ_MP (@lem7002487 A B y s _93304 t R x' x h1 h2 h3 h4) (@lem7000498 A B _93304 t R x' x h2)). Qed.
Lemma lem7002489 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term987 A B s _93304 t R x' x) : (term963 A s x') = False.
Proof. exact (prop_ext (fun h3 : term963 A s x' => @lem7001141 A B s _93304 t R x' x h1 h2) (fun h3 : False => @lem7000426 A s x' h1)). Qed.
Lemma lem7002490 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term987 A B s _93304 t R x' x) : False.
Proof. exact (EQ_MP (@lem7002489 A B s _93304 t R x' x h1 h2) (@lem7000426 A s x' h1)). Qed.
Lemma lem7002491 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term380 A B R x' x) (h3 : term940 A B x y t R s) (h4 : term981 A B s _93304 t R x' x) : (term380 A B R x' x) = False.
Proof. exact (prop_ext (fun h5 : term380 A B R x' x => @lem7002484 A B y s _93304 t R x' x h1 h2 h3 h4) (fun h5 : False => @lem7000308 A B R x' x h2)). Qed.
Lemma lem7002492 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term380 A B R x' x) (h3 : term940 A B x y t R s) (h4 : term981 A B s _93304 t R x' x) : False.
Proof. exact (EQ_MP (@lem7002491 A B y s _93304 t R x' x h1 h2 h3 h4) (@lem7000308 A B R x' x h2)). Qed.
Lemma lem7002493 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term981 A B s _93304 t R x' x) : (term963 A s x') = False.
Proof. exact (prop_ext (fun h3 : term963 A s x' => @lem7002486 A B s _93304 t R x' x h1 h2) (fun h3 : False => @lem7000036 A s x' h1)). Qed.
Lemma lem7002494 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term981 A B s _93304 t R x' x) : False.
Proof. exact (EQ_MP (@lem7002493 A B s _93304 t R x' x h1 h2) (@lem7000036 A s x' h1)). Qed.
Lemma lem7002495 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term983 A B _93304 t R x' x) (h3 : term940 A B x y t R s) (h4 : term987 A B s _93304 t R x' x) : (term983 A B _93304 t R x' x) = False.
Proof. exact (prop_ext (fun h5 : term983 A B _93304 t R x' x => @lem7002488 A B y s _93304 t R x' x h1 h2 h3 h4) (fun h5 : False => @lem6999764 A B _93304 t R x' x h2)). Qed.
Lemma lem7002496 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term983 A B _93304 t R x' x) (h3 : term940 A B x y t R s) (h4 : term987 A B s _93304 t R x' x) : False.
Proof. exact (EQ_MP (@lem7002495 A B y s _93304 t R x' x h1 h2 h3 h4) (@lem6999764 A B _93304 t R x' x h2)). Qed.
Lemma lem7002497 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term987 A B s _93304 t R x' x) : (term963 A s x') = False.
Proof. exact (prop_ext (fun h3 : term963 A s x' => @lem7002490 A B s _93304 t R x' x h1 h2) (fun h3 : False => @lem6999492 A s x' h1)). Qed.
Lemma lem7002498 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term987 A B s _93304 t R x' x) : False.
Proof. exact (EQ_MP (@lem7002497 A B s _93304 t R x' x h1 h2) (@lem6999492 A s x' h1)). Qed.
Lemma lem7002499 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term380 A B R x' x) (h3 : term940 A B x y t R s) (h4 : term981 A B s _93304 t R x' x) : (term380 A B R x' x) = False.
Proof. exact (prop_ext (fun h5 : term380 A B R x' x => @lem7002492 A B y s _93304 t R x' x h1 h2 h3 h4) (fun h5 : False => @lem7000308 A B R x' x h2)). Qed.
Lemma lem7002500 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term380 A B R x' x) (h3 : term940 A B x y t R s) (h4 : term981 A B s _93304 t R x' x) : False.
Proof. exact (EQ_MP (@lem7002499 A B y s _93304 t R x' x h1 h2 h3 h4) (@lem7000308 A B R x' x h2)). Qed.
Lemma lem7002501 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term981 A B s _93304 t R x' x) : (term963 A s x') = False.
Proof. exact (prop_ext (fun h3 : term963 A s x' => @lem7002494 A B s _93304 t R x' x h1 h2) (fun h3 : False => @lem7000036 A s x' h1)). Qed.
Lemma lem7002502 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term981 A B s _93304 t R x' x) : False.
Proof. exact (EQ_MP (@lem7002501 A B s _93304 t R x' x h1 h2) (@lem7000036 A s x' h1)). Qed.
Lemma lem7002503 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term983 A B _93304 t R x' x) (h3 : term940 A B x y t R s) (h4 : term987 A B s _93304 t R x' x) : (term983 A B _93304 t R x' x) = False.
Proof. exact (prop_ext (fun h5 : term983 A B _93304 t R x' x => @lem7002496 A B y s _93304 t R x' x h1 h2 h3 h4) (fun h5 : False => @lem6999764 A B _93304 t R x' x h2)). Qed.
Lemma lem7002504 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term983 A B _93304 t R x' x) (h3 : term940 A B x y t R s) (h4 : term987 A B s _93304 t R x' x) : False.
Proof. exact (EQ_MP (@lem7002503 A B y s _93304 t R x' x h1 h2 h3 h4) (@lem6999764 A B _93304 t R x' x h2)). Qed.
Lemma lem7002505 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term987 A B s _93304 t R x' x) : (term963 A s x') = False.
Proof. exact (prop_ext (fun h3 : term963 A s x' => @lem7002498 A B s _93304 t R x' x h1 h2) (fun h3 : False => @lem6999492 A s x' h1)). Qed.
Lemma lem7002506 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term963 A s x') (h2 : term987 A B s _93304 t R x' x) : False.
Proof. exact (EQ_MP (@lem7002505 A B s _93304 t R x' x h1 h2) (@lem6999492 A s x' h1)). Qed.
Lemma lem7002507 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term940 A B x y t R s) (h3 : term981 A B s _93304 t R x' x) : False.
Proof. exact (or_elim (@lem6999216 A B s _93304 t R x' x h3) (fun h0 : term963 A s x' => @lem7002502 A B s _93304 t R x' x h0 h3) (fun h0 : term380 A B R x' x => @lem7002500 A B y s _93304 t R x' x h1 h0 h2 h3)). Qed.
Lemma lem7002508 {A B : Type'} (y : A -> B) (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x' : A) (x : B) (h1 : term728 A B _93304) (h2 : term940 A B x y t R s) (h3 : term987 A B s _93304 t R x' x) : False.
Proof. exact (or_elim (@lem6999209 A B s _93304 t R x' x h3) (fun h0 : term963 A s x' => @lem7002506 A B s _93304 t R x' x h0 h3) (fun h0 : term983 A B _93304 t R x' x => @lem7002504 A B y s _93304 t R x' x h1 h0 h2 h3)). Qed.
Lemma lem7002509 {A B : Type'} (_93304 : type830 A B) (x' : A) (x : B) (y : A -> B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term728 A B _93304) (h2 : term774 A B s _93304 t R x' x) (h3 : term940 A B x y t R s) : False.
Proof. exact (or_elim (@lem6999037 A B s _93304 t R x' x h2) (fun h0 : term987 A B s _93304 t R x' x => @lem7002508 A B y s _93304 t R x' x h1 h3 h0) (fun h0 : term981 A B s _93304 t R x' x => @lem7002507 A B y s _93304 t R x' x h1 h3 h0)). Qed.
Lemma lem7002510 {A B : Type'} (_93304 : type830 A B) (x' : A) (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term728 A B _93304) (h2 : term774 A B s _93304 t R x' x) (h3 : term639 A B x t R s) : False.
Proof. exact (ex_elim (@lem6998714 A B x t R s h3) (fun y : A -> B => fun h0 : term942 A B x t R s y => @lem7002509 A B _93304 x' x y t R s h1 h2 h0)). Qed.
Lemma lem7002511 {A B : Type'} (_93304 : type830 A B) (x' : A) (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term728 A B _93304) (h2 : term774 A B s _93304 t R x' x) (h3 : term639 A B x t R s) : (term774 A B s _93304 t R x' x) = False.
Proof. exact (prop_ext (fun h4 : term774 A B s _93304 t R x' x => @lem7002510 A B _93304 x' x t R s h1 h2 h3) (fun h4 : False => @lem6998054 A B s _93304 t R x' x h2)). Qed.
Lemma lem7002512 {A B : Type'} (_93304 : type830 A B) (x' : A) (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term728 A B _93304) (h2 : term774 A B s _93304 t R x' x) (h3 : term639 A B x t R s) : False.
Proof. exact (EQ_MP (@lem7002511 A B _93304 x' x t R s h1 h2 h3) (@lem6998054 A B s _93304 t R x' x h2)). Qed.
Lemma lem7002513 {A B : Type'} (x' : A) (_93304 : type830 A B) (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term728 A B _93304) (h2 : term639 A B x t R s) : term773 A B s _93304 t R x' x.
Proof. exact (fun h0 : term774 A B s _93304 t R x' x => @lem7002512 A B _93304 x' x t R s h1 h0 h2). Qed.
Lemma lem7002514 {A B : Type'} (x' : A) (_93304 : type830 A B) (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term728 A B _93304) (h2 : term639 A B x t R s) : (term660 A B s R x' x) = (term731 A B s _93304 t R x' x).
Proof. exact (EQ_MP (@lem6998053 A B s _93304 t R x' x) (@lem7002513 A B x' _93304 x t R s h1 h2)). Qed.
Lemma lem7002519 {A B : Type'} (_93304 : type830 A B) (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term728 A B _93304) (h2 : term639 A B x t R s) : term733 A B s _93304 t R x.
Proof. exact (fun x' : A => @lem7002514 A B x' _93304 x t R s h1 h2). Qed.
Lemma lem7002520 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (_93304 : type830 A B) (h1 : term728 A B _93304) : term734 A B s _93304 t R x.
Proof. exact (fun h0 : term639 A B x t R s => @lem7002519 A B _93304 x t R s h1 h0). Qed.
Lemma lem7002521 {A B : Type'} (s : A -> Prop) (_93304 : type830 A B) (t : B -> Prop) (R : type1413 A B) (x : B) : term753 A B s _93304 t R x.
Proof. exact (fun h0 : term728 A B _93304 => @lem7002520 A B s t R x _93304 h0). Qed.
Lemma lem7002526 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term756 A B s t R x.
Proof. exact (fun _93304 : type830 A B => @lem7002521 A B s _93304 t R x). Qed.
Lemma lem7002531 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : B) : term760 A B t R x.
Proof. exact (fun s : A -> Prop => @lem7002526 A B s t R x). Qed.
Lemma lem7002536 {A B : Type'} (R : type1413 A B) (x : B) : term764 A B R x.
Proof. exact (fun t : B -> Prop => @lem7002531 A B t R x). Qed.
Lemma lem7002541 {A B : Type'} (x : B) : term768 A B x.
Proof. exact (fun R : type1413 A B => @lem7002536 A B R x). Qed.
Lemma lem7002546 {A B : Type'} : term772 A B.
Proof. exact (fun x : B => @lem7002541 A B x). Qed.
Lemma lem7002547 {A B : Type'} : term771 A B.
Proof. exact (EQ_MP (@lem6998047 A B) (@lem7002546 A B)). Qed.
Lemma lem7002548 {A B : Type'} (x : B) : term1239 A B x.
Proof. exact (@lem7002547 A B x). Qed.
Lemma lem7002549 {A B : Type'} (x : B) : (term1239 A B x) = (term767 A B x).
Proof. exact (eq_refl (term1239 A B x)). Qed.
Lemma lem7002550 {A B : Type'} (x : B) : term767 A B x.
Proof. exact (EQ_MP (@lem7002549 A B x) (@lem7002548 A B x)). Qed.
Lemma lem7002551 {A B : Type'} (x : B) (R : type1413 A B) : term1240 A B x R.
Proof. exact (@lem7002550 A B x R). Qed.
Lemma lem7002552 {A B : Type'} (R : type1413 A B) (x : B) : (term1240 A B x R) = (term763 A B R x).
Proof. exact (eq_refl (term1240 A B x R)). Qed.
Lemma lem7002553 {A B : Type'} (R : type1413 A B) (x : B) : term763 A B R x.
Proof. exact (EQ_MP (@lem7002552 A B R x) (@lem7002551 A B x R)). Qed.
Lemma lem7002554 {A B : Type'} (R : type1413 A B) (x : B) (t : B -> Prop) : term1241 A B R x t.
Proof. exact (@lem7002553 A B R x t). Qed.
Lemma lem7002555 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : B) : (term1241 A B R x t) = (term759 A B t R x).
Proof. exact (eq_refl (term1241 A B R x t)). Qed.
Lemma lem7002556 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : B) : term759 A B t R x.
Proof. exact (EQ_MP (@lem7002555 A B t R x) (@lem7002554 A B R x t)). Qed.
Lemma lem7002557 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : B) (s : A -> Prop) : term1242 A B t R x s.
Proof. exact (@lem7002556 A B t R x s). Qed.
Lemma lem7002558 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : (term1242 A B t R x s) = (term740 A B s t R x).
Proof. exact (eq_refl (term1242 A B t R x s)). Qed.
Lemma lem7002559 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term740 A B s t R x.
Proof. exact (EQ_MP (@lem7002558 A B s t R x) (@lem7002557 A B t R x s)). Qed.
Lemma lem7002561 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term681 A B s t R x.
Proof. exact (@lem6997754 A B s t R x (@lem7002559 A B s t R x)). Qed.
Lemma lem7002562 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term682 A B s t R x) : False.
Proof. exact (@lem7002561 A B s t R x (@lem6997600 A B s t R x h1)). Qed.
Lemma lem7002563 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term682 A B s t R x) : (term682 A B s t R x) = False.
Proof. exact (prop_ext (fun h2 : term682 A B s t R x => @lem7002562 A B s t R x h1) (fun h2 : False => @lem6997600 A B s t R x h1)). Qed.
Lemma lem7002564 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) (h1 : term682 A B s t R x) : False.
Proof. exact (EQ_MP (@lem7002563 A B s t R x h1) (@lem6997600 A B s t R x h1)). Qed.
Lemma lem7002565 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term681 A B s t R x.
Proof. exact (fun h0 : term682 A B s t R x => @lem7002564 A B s t R x h0). Qed.
Lemma lem7002566 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term680 A B s t R x.
Proof. exact (EQ_MP (@lem6997599 A B s t R x) (@lem7002565 A B s t R x)). Qed.
Lemma lem7002567 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term627 A B s t R x.
Proof. exact (EQ_MP (@lem6997595 A B s t R x) (@lem7002566 A B s t R x)). Qed.
Lemma lem7002568 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : B) : term626 A B s t R x.
Proof. exact (EQ_MP (@lem6997421 A B s t R x) (@lem7002567 A B s t R x)). Qed.
Lemma lem7002569 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (x : B) (t : B -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) (h3 : @IN B x t) : (term623 A B s R x) = (term101 A B s t R x).
Proof. exact (@lem7002568 A B s t R x (@lem6997370 A B R s x t h1 h2 h3)). Qed.
Lemma lem7002570 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (x : B) (t : B -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) (h3 : @IN B x t) : (term1243 A B s R x) = (term103 A B s t R x).
Proof. exact (MK_COMB (@lem6997358 A) (@lem7002569 A B R s x t h1 h2 h3)). Qed.
Lemma lem7002571 {A B : Type'} (g : A -> nat) (R : type1413 A B) (s : A -> Prop) (x : B) (t : B -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) (h3 : @IN B x t) : (term610 A B s R x g) = (term105 A B s t R x g).
Proof. exact (MK_COMB (@lem7002570 A B R s x t h1 h2 h3) (@lem6997357 A g)). Qed.
Lemma lem7002572 {A B : Type'} (g : A -> nat) (R : type1413 A B) (s : A -> Prop) (x : B) (t : B -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) (h3 : @IN B x t) : (term609 A B s R g x) = (term616 A B s t R g x).
Proof. exact (EQ_MP (@lem6997356 A B s t R g x) (@lem7002571 A B g R s x t h1 h2 h3)). Qed.
Lemma lem7002573 {A B : Type'} (g : A -> nat) (R : type1413 A B) (s : A -> Prop) (x : B) (t : B -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) (h3 : @IN B x t) : (@IN B x t) = ((term609 A B s R g x) = (term616 A B s t R g x)).
Proof. exact (prop_ext (fun h4 : @IN B x t => @lem7002572 A B g R s x t h1 h2 h3) (fun h4 : (term609 A B s R g x) = (term616 A B s t R g x) => @lem6997306 B x t h3)). Qed.
Lemma lem7002574 {A B : Type'} (g : A -> nat) (R : type1413 A B) (s : A -> Prop) (x : B) (t : B -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) (h3 : @IN B x t) : (term609 A B s R g x) = (term616 A B s t R g x).
Proof. exact (EQ_MP (@lem7002573 A B g R s x t h1 h2 h3) (@lem6997306 B x t h3)). Qed.
Lemma lem7002575 {A B : Type'} (g : A -> nat) (x : B) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : term1244 A B s t R g x.
Proof. exact (fun h0 : @IN B x t => @lem7002574 A B g R s x t h1 h2 h0). Qed.
Lemma lem7002580 {A B : Type'} (g : A -> nat) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : term1245 A B s t R g.
Proof. exact (fun x : B => @lem7002575 A B g x t R s h1 h2). Qed.
Lemma lem7002581 {A B : Type'} (g : A -> nat) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : (term115 A B t s R g) = (term109 A B s t R g).
Proof. exact (@lem6997305 A B s t R g (@lem7002580 A B g t R s h1 h2)). Qed.
Lemma lem7002582 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> nat) (h1 : term34 A B s t R) (h2 : @FINITE A s) (h3 : (term109 A B s t R g) = (@nsum A s g)) : (term115 A B t s R g) = (@nsum A s g).
Proof. exact (EQ_MP (@lem6997301 A B t R s g h3) (@lem7002581 A B g t R s h1 h2)). Qed.
Lemma lem7002583 {A B : Type'} (g : A -> nat) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : term1246 A B t R s g.
Proof. exact (fun h0 : (term109 A B s t R g) = (@nsum A s g) => @lem7002582 A B t R s g h1 h2 h0). Qed.
Lemma lem7002584 {A B : Type'} (g : A -> nat) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : term1247 A B t R s g.
Proof. exact (conj (@lem6997286 A B t R s h1 h2) (@lem7002583 A B g t R s h1 h2)). Qed.
Lemma lem7002585 {A B : Type'} (g : A -> nat) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : term117 A B t R s g.
Proof. exact (@lem6994987 A B t R s g (@lem7002584 A B g t R s h1 h2)). Qed.
Lemma lem7002586 {A B : Type'} (g : A -> nat) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : term116 A B t R s g.
Proof. exact (EQ_MP (@lem6994984 A B t R g s h2) (@lem7002585 A B g t R s h1 h2)). Qed.
Lemma lem7002587 {A B : Type'} (g : A -> nat) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : (term115 A B t s R g) = (@nsum A s g).
Proof. exact (@lem7002586 A B g t R s h1 h2 (@lem6994795 A B t R s g)). Qed.
Lemma lem7002588 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (h1 : term33 A B s t R) : term34 A B s t R.
Proof. exact (proj2 (@lem6994796 A B s t R h1)). Qed.
Lemma lem7002589 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (h1 : term33 A B s t R) : @FINITE A s.
Proof. exact (proj1 (@lem6994796 A B s t R h1)). Qed.
Lemma lem7002590 {A B : Type'} (g : A -> nat) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : (term34 A B s t R) = ((term115 A B t s R g) = (@nsum A s g)).
Proof. exact (prop_ext (fun h3 : term34 A B s t R => @lem7002587 A B g t R s h1 h2) (fun h3 : (term115 A B t s R g) = (@nsum A s g) => @lem6994797 A B s t R h1)). Qed.
Lemma lem7002591 {A B : Type'} (g : A -> nat) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : (term115 A B t s R g) = (@nsum A s g).
Proof. exact (EQ_MP (@lem7002590 A B g t R s h1 h2) (@lem6994797 A B s t R h1)). Qed.
Lemma lem7002592 {A B : Type'} (g : A -> nat) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : (@FINITE A s) = ((term115 A B t s R g) = (@nsum A s g)).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem7002591 A B g t R s h1 h2) (fun h3 : (term115 A B t s R g) = (@nsum A s g) => @lem6994798 A s h2)). Qed.
Lemma lem7002593 {A B : Type'} (g : A -> nat) (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (h1 : term34 A B s t R) (h2 : @FINITE A s) : (term115 A B t s R g) = (@nsum A s g).
Proof. exact (EQ_MP (@lem7002592 A B g t R s h1 h2) (@lem6994798 A s h2)). Qed.
Lemma lem7002594 {A B : Type'} (g : A -> nat) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (h1 : @FINITE A s) (h2 : term33 A B s t R) : (term34 A B s t R) = ((term115 A B t s R g) = (@nsum A s g)).
Proof. exact (prop_ext (fun h3 : term34 A B s t R => @lem7002593 A B g t R s h3 h1) (fun h3 : (term115 A B t s R g) = (@nsum A s g) => @lem7002588 A B s t R h2)). Qed.
Lemma lem7002595 {A B : Type'} (g : A -> nat) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (h1 : @FINITE A s) (h2 : term33 A B s t R) : (term115 A B t s R g) = (@nsum A s g).
Proof. exact (EQ_MP (@lem7002594 A B g s t R h1 h2) (@lem7002588 A B s t R h2)). Qed.
Lemma lem7002596 {A B : Type'} (g : A -> nat) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (h1 : term33 A B s t R) : (@FINITE A s) = ((term115 A B t s R g) = (@nsum A s g)).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem7002595 A B g s t R h2 h1) (fun h2 : (term115 A B t s R g) = (@nsum A s g) => @lem7002589 A B s t R h1)). Qed.
Lemma lem7002597 {A B : Type'} (g : A -> nat) (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (h1 : term33 A B s t R) : (term115 A B t s R g) = (@nsum A s g).
Proof. exact (EQ_MP (@lem7002596 A B g s t R h1) (@lem7002589 A B s t R h1)). Qed.
Lemma lem7002598 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (s : A -> Prop) (g : A -> nat) : term1248 A B t R s g.
Proof. exact (fun h0 : term33 A B s t R => @lem7002597 A B g s t R h0). Qed.
Lemma lem7002603 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (g : A -> nat) : term1249 A B R s g.
Proof. exact (fun t : B -> Prop => @lem7002598 A B t R s g). Qed.
Lemma lem7002608 {A B : Type'} (R : type1413 A B) (g : A -> nat) : term1250 A B R g.
Proof. exact (fun s : A -> Prop => @lem7002603 A B R s g). Qed.
Lemma lem7002613 {A B : Type'} (R : type1413 A B) : term1251 A B R.
Proof. exact (fun g : A -> nat => @lem7002608 A B R g). Qed.
Lemma lem7002618 {A B : Type'} : term1252 A B.
Proof. exact (fun R : type1413 A B => @lem7002613 A B R). Qed.
