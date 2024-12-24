Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RESTRICTION_COMPOSE_term_abbrevs.
Require Import RESTRICTION_COMPOSE_LEFT_spec.
Require Import RESTRICTION_COMPOSE_RIGHT_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem4393762 {A B C : Type'} (f : A -> B) : term0 A B C f.
Proof. exact (@lem4393235 A B C f). Qed.
Lemma lem4393763 {A B C : Type'} (f : A -> B) : (term0 A B C f) = (term1 A B C f).
Proof. exact (eq_refl (term0 A B C f)). Qed.
Lemma lem4393764 {A B C : Type'} (f : A -> B) : term1 A B C f.
Proof. exact (EQ_MP (@lem4393763 A B C f) (@lem4393762 A B C f)). Qed.
Lemma lem4393765 {A B C : Type'} (f : A -> B) (g : B -> C) : term2 A B C f g.
Proof. exact (@lem4393764 A B C f g). Qed.
Lemma lem4393766 {A B C : Type'} (g : B -> C) (f : A -> B) : (term2 A B C f g) = (term3 A B C g f).
Proof. exact (eq_refl (term2 A B C f g)). Qed.
Lemma lem4393767 {A B C : Type'} (g : B -> C) (f : A -> B) : term3 A B C g f.
Proof. exact (EQ_MP (@lem4393766 A B C g f) (@lem4393765 A B C f g)). Qed.
Lemma lem4393768 {A B C : Type'} (g : B -> C) (f : A -> B) (s : A -> Prop) : term4 A B C g f s.
Proof. exact (@lem4393767 A B C g f s). Qed.
Lemma lem4393769 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) : (term4 A B C g f s) = ((term5 A B C g s f) = (term6 A B C s g f)).
Proof. exact (eq_refl (term4 A B C g f s)). Qed.
Lemma lem4393771 {A B C : Type'} (f : A -> B) : term7 A B C f.
Proof. exact (@lem4393761 A B C f). Qed.
Lemma lem4393772 {A B C : Type'} (f : A -> B) : (term7 A B C f) = (term8 A B C f).
Proof. exact (eq_refl (term7 A B C f)). Qed.
Lemma lem4393773 {A B C : Type'} (f : A -> B) : term8 A B C f.
Proof. exact (EQ_MP (@lem4393772 A B C f) (@lem4393771 A B C f)). Qed.
Lemma lem4393774 {A B C : Type'} (f : A -> B) (g : B -> C) : term9 A B C f g.
Proof. exact (@lem4393773 A B C f g). Qed.
Lemma lem4393775 {A B C : Type'} (g : B -> C) (f : A -> B) : (term9 A B C f g) = (term10 A B C g f).
Proof. exact (eq_refl (term9 A B C f g)). Qed.
Lemma lem4393776 {A B C : Type'} (g : B -> C) (f : A -> B) : term10 A B C g f.
Proof. exact (EQ_MP (@lem4393775 A B C g f) (@lem4393774 A B C f g)). Qed.
Lemma lem4393777 {A B C : Type'} (g : B -> C) (f : A -> B) (s : A -> Prop) : term11 A B C g f s.
Proof. exact (@lem4393776 A B C g f s). Qed.
Lemma lem4393778 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) : (term11 A B C g f s) = (term12 A B C s g f).
Proof. exact (eq_refl (term11 A B C g f s)). Qed.
Lemma lem4393779 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) : term12 A B C s g f.
Proof. exact (EQ_MP (@lem4393778 A B C s g f) (@lem4393777 A B C g f s)). Qed.
Lemma lem4393780 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (t : B -> Prop) : term13 A B C s g f t.
Proof. exact (@lem4393779 A B C s g f t). Qed.
Lemma lem4393781 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term13 A B C s g f t) = (term14 A B C t s g f).
Proof. exact (eq_refl (term13 A B C s g f t)). Qed.
Lemma lem4393782 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) : term14 A B C t s g f.
Proof. exact (EQ_MP (@lem4393781 A B C t s g f) (@lem4393780 A B C s g f t)). Qed.
Lemma lem4393783 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B f s t) : term15 A B f s t.
Proof. exact (h1). Qed.
Lemma lem4393784 {A B C : Type'} (g : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B f s t) : (term16 A B C s t g f) = (term6 A B C s g f).
Proof. exact (@lem4393782 A B C t s g f (@lem4393783 A B f s t h1)). Qed.
Lemma lem4393809 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term17 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4393810 (p : Prop) (q : Prop) (p' : Prop) : term18 p q p'.
Proof. exact (fun q' : Prop => @lem4393809 p q p' q'). Qed.
Lemma lem4393811 (p : Prop) (q : Prop) : term19 p q.
Proof. exact (fun p' : Prop => @lem4393810 p q p'). Qed.
Lemma lem4393812 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) : term20 A B C t s g f.
Proof. exact (@lem4393811 (term15 A B f s t) ((term21 A B C t g s f) = (term6 A B C s g f))). Qed.
Lemma lem4393813 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) : term22 A B C t s g f p'.
Proof. exact (@lem4393812 A B C t s g f p'). Qed.
Lemma lem4393814 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) : (term22 A B C t s g f p') = (term23 A B C t s g f p').
Proof. exact (eq_refl (term22 A B C t s g f p')). Qed.
Lemma lem4393815 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) : term23 A B C t s g f p'.
Proof. exact (EQ_MP (@lem4393814 A B C t s g f p') (@lem4393813 A B C t s g f p')). Qed.
Lemma lem4393816 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) (q' : Prop) : term24 A B C t s g f p' q'.
Proof. exact (@lem4393815 A B C t s g f p' q'). Qed.
Lemma lem4393817 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) (q' : Prop) : (term24 A B C t s g f p' q') = (term25 A B C t s g f p' q').
Proof. exact (eq_refl (term24 A B C t s g f p' q')). Qed.
Lemma lem4393818 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) (q' : Prop) : term25 A B C t s g f p' q'.
Proof. exact (EQ_MP (@lem4393817 A B C t s g f p' q') (@lem4393816 A B C t s g f p' q')). Qed.
Lemma lem4393819 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term15 A B f s t) = (term15 A B f s t).
Proof. exact (eq_refl (term15 A B f s t)). Qed.
Lemma lem4393820 {A B C : Type'} (g : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (q' : Prop) : term26 A B C g f s t q'.
Proof. exact (@lem4393818 A B C t s g f (term15 A B f s t) q'). Qed.
Lemma lem4393821 {A B C : Type'} (g : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (q' : Prop) : term27 A B C g f s t q'.
Proof. exact (@lem4393820 A B C g f s t q' (@lem4393819 A B f s t)). Qed.
Lemma lem4393822 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B f s t) : term15 A B f s t.
Proof. exact (h1). Qed.
Lemma lem4393823 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term15 A B f s t) = ((term15 A B f s t) = True).
Proof. exact (@lem7 (term15 A B f s t)). Qed.
Lemma lem4393834 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) : (term5 A B C g s f) = (term6 A B C s g f).
Proof. exact (EQ_MP (@lem4393769 A B C s g f) (@lem4393768 A B C g f s)). Qed.
Lemma lem4393835 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) : (term5 A B C g s f) = (term6 A B C s g f).
Proof. exact (@lem4393834 A B C s g f). Qed.
Lemma lem4393836 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (f : A -> B) : (term21 A B C t g s f) = (term16 A B C s t g f).
Proof. exact (@lem4393835 A B C s (@RESTRICTION B C t g) f). Qed.
Lemma lem4393838 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) : term14 A B C t s g f.
Proof. exact (fun h0 : term15 A B f s t => @lem4393784 A B C g f s t h0). Qed.
Lemma lem4393839 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) : term14 A B C t s g f.
Proof. exact (@lem4393838 A B C t s g f). Qed.
Lemma lem4393841 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B f s t) : (term15 A B f s t) = True.
Proof. exact (EQ_MP (@lem4393823 A B f s t) (@lem4393822 A B f s t h1)). Qed.
Lemma lem4393842 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B f s t) : True = (term15 A B f s t).
Proof. exact (SYM (@lem4393841 A B f s t h1)). Qed.
Lemma lem4393843 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B f s t) : term15 A B f s t.
Proof. exact (EQ_MP (@lem4393842 A B f s t h1) (@lem0)). Qed.
Lemma lem4393844 {A B C : Type'} (g : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B f s t) : (term16 A B C s t g f) = (term6 A B C s g f).
Proof. exact (@lem4393839 A B C t s g f (@lem4393843 A B f s t h1)). Qed.
Lemma lem4393845 {A B C : Type'} (g : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B f s t) : (term21 A B C t g s f) = (term6 A B C s g f).
Proof. exact (TRANS (@lem4393836 A B C s t g f) (@lem4393844 A B C g f s t h1)). Qed.
Lemma lem4393846 {A C : Type'} : (@eq (A -> C)) = (@eq (A -> C)).
Proof. exact (eq_refl (@eq (A -> C))). Qed.
Lemma lem4393847 {A B C : Type'} (g : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B f s t) : (term28 A B C t g s f) = (term29 A B C s g f).
Proof. exact (MK_COMB (@lem4393846 A C) (@lem4393845 A B C g f s t h1)). Qed.
Lemma lem4393848 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) : (term6 A B C s g f) = (term6 A B C s g f).
Proof. exact (eq_refl (term6 A B C s g f)). Qed.
Lemma lem4393849 {A B C : Type'} (g : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B f s t) : ((term21 A B C t g s f) = (term6 A B C s g f)) = ((term6 A B C s g f) = (term6 A B C s g f)).
Proof. exact (MK_COMB (@lem4393847 A B C g f s t h1) (@lem4393848 A B C s g f)). Qed.
Lemma lem4393851 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4393852 {A C : Type'} (x : A -> C) : (x = x) = True.
Proof. exact (@lem4393851 (A -> C) x). Qed.
Lemma lem4393853 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term6 A B C s g f) = (term6 A B C s g f)) = True.
Proof. exact (@lem4393852 A C (term6 A B C s g f)). Qed.
Lemma lem4393854 {A B C : Type'} (g : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B f s t) : ((term21 A B C t g s f) = (term6 A B C s g f)) = True.
Proof. exact (TRANS (@lem4393849 A B C g f s t h1) (@lem4393853 A B C s g f)). Qed.
Lemma lem4393855 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) : term30 A B C t s g f.
Proof. exact (fun h0 : term15 A B f s t => @lem4393854 A B C g f s t h0). Qed.
Lemma lem4393856 {A B C : Type'} (g : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : term31 A B C g f s t.
Proof. exact (@lem4393821 A B C g f s t True). Qed.
Lemma lem4393857 {A B C : Type'} (g : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term32 A B C t s g f) = (term33 A B f s t).
Proof. exact (@lem4393856 A B C g f s t (@lem4393855 A B C t s g f)). Qed.
Lemma lem4393859 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4393860 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term33 A B f s t) = True.
Proof. exact (@lem4393859 (term15 A B f s t)). Qed.
Lemma lem4393861 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term32 A B C t s g f) = True.
Proof. exact (TRANS (@lem4393857 A B C g f s t) (@lem4393860 A B f s t)). Qed.
Lemma lem4393862 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) : (term34 A B C s g f) = (term35 B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4393861 A B C t s g f)). Qed.
Lemma lem4393863 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4393864 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) : (term36 A B C s g f) = (term37 B).
Proof. exact (MK_COMB (@lem4393863 B) (@lem4393862 A B C s g f)). Qed.
Lemma lem4393866 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4393867 {B : Type'} (t : Prop) : (term39 B t) = t.
Proof. exact (@lem4393866 (B -> Prop) t). Qed.
Lemma lem4393868 {B : Type'} : (term37 B) = True.
Proof. exact (@lem4393867 B True). Qed.
Lemma lem4393869 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) : (term36 A B C s g f) = True.
Proof. exact (TRANS (@lem4393864 A B C s g f) (@lem4393868 B)). Qed.
Lemma lem4393870 {A B C : Type'} (g : B -> C) (f : A -> B) : (term40 A B C g f) = (term35 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4393869 A B C s g f)). Qed.
Lemma lem4393871 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4393872 {A B C : Type'} (g : B -> C) (f : A -> B) : (term41 A B C g f) = (term37 A).
Proof. exact (MK_COMB (@lem4393871 A) (@lem4393870 A B C g f)). Qed.
Lemma lem4393874 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4393875 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (@lem4393874 (A -> Prop) t). Qed.
Lemma lem4393876 {A : Type'} : (term37 A) = True.
Proof. exact (@lem4393875 A True). Qed.
Lemma lem4393877 {A B C : Type'} (g : B -> C) (f : A -> B) : (term41 A B C g f) = True.
Proof. exact (TRANS (@lem4393872 A B C g f) (@lem4393876 A)). Qed.
Lemma lem4393878 {A B C : Type'} (f : A -> B) : (term42 A B C f) = (term43 B C).
Proof. exact (fun_ext (fun g : B -> C => @lem4393877 A B C g f)). Qed.
Lemma lem4393879 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem4393880 {A B C : Type'} (f : A -> B) : (term44 A B C f) = (term45 B C).
Proof. exact (MK_COMB (@lem4393879 B C) (@lem4393878 A B C f)). Qed.
Lemma lem4393882 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4393883 {B C : Type'} (t : Prop) : (term46 B C t) = t.
Proof. exact (@lem4393882 (B -> C) t). Qed.
Lemma lem4393884 {B C : Type'} : (term45 B C) = True.
Proof. exact (@lem4393883 B C True). Qed.
Lemma lem4393885 {A B C : Type'} (f : A -> B) : (term44 A B C f) = True.
Proof. exact (TRANS (@lem4393880 A B C f) (@lem4393884 B C)). Qed.
Lemma lem4393886 {A B C : Type'} : (term47 A B C) = (term43 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4393885 A B C f)). Qed.
Lemma lem4393887 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4393888 {A B C : Type'} : (term48 A B C) = (term45 A B).
Proof. exact (MK_COMB (@lem4393887 A B) (@lem4393886 A B C)). Qed.
Lemma lem4393890 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4393891 {A B : Type'} (t : Prop) : (term46 A B t) = t.
Proof. exact (@lem4393890 (A -> B) t). Qed.
Lemma lem4393892 {A B : Type'} : (term45 A B) = True.
Proof. exact (@lem4393891 A B True). Qed.
Lemma lem4393893 {A B C : Type'} : (term48 A B C) = True.
Proof. exact (TRANS (@lem4393888 A B C) (@lem4393892 A B)). Qed.
Lemma lem4393894 {A B C : Type'} : True = (term48 A B C).
Proof. exact (SYM (@lem4393893 A B C)). Qed.
Lemma lem4393895 {A B C : Type'} : term48 A B C.
Proof. exact (EQ_MP (@lem4393894 A B C) (@lem0)). Qed.
