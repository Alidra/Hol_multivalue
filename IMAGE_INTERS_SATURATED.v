Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_INTERS_SATURATED_term_abbrevs.
Require Import IMAGE_INTERS_SATURATED_GEN_spec.
Require Import IN_UNIV_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import SUBSET_UNIV_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem3556762 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem3556763 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term1 A B f.
Proof. exact (@lem3556762 A B h1 f). Qed.
Lemma lem3556764 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem3556765 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term2 A B f.
Proof. exact (EQ_MP (@lem3556764 A B f) (@lem3556763 A B f h1)). Qed.
Lemma lem3556766 {A B : Type'} (f : A -> B) (g : type686 A) (h1 : term0 A B) : term3 A B f g.
Proof. exact (@lem3556765 A B f h1 g). Qed.
Lemma lem3556767 {A B : Type'} (f : A -> B) (g : type686 A) : (term3 A B f g) = (term4 A B f g).
Proof. exact (eq_refl (term3 A B f g)). Qed.
Lemma lem3556768 {A B : Type'} (f : A -> B) (g : type686 A) (h1 : term0 A B) : term4 A B f g.
Proof. exact (EQ_MP (@lem3556767 A B f g) (@lem3556766 A B f g h1)). Qed.
Lemma lem3556769 {A B : Type'} (f : A -> B) (g : type686 A) (s : A -> Prop) (h1 : term0 A B) : term5 A B f g s.
Proof. exact (@lem3556768 A B f g h1 s). Qed.
Lemma lem3556770 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : type686 A) : (term5 A B f g s) = (term6 A B s f g).
Proof. exact (eq_refl (term5 A B f g s)). Qed.
Lemma lem3556771 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : type686 A) (h1 : term0 A B) : term6 A B s f g.
Proof. exact (EQ_MP (@lem3556770 A B s f g) (@lem3556769 A B f g s h1)). Qed.
Lemma lem3556772 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : type686 A) (u : A -> Prop) (h1 : term0 A B) : term7 A B s f g u.
Proof. exact (@lem3556771 A B s f g h1 u). Qed.
Lemma lem3556773 {A B : Type'} (s : A -> Prop) (u : A -> Prop) (f : A -> B) (g : type686 A) : (term7 A B s f g u) = (term8 A B s u f g).
Proof. exact (eq_refl (term7 A B s f g u)). Qed.
Lemma lem3556774 {A B : Type'} (s : A -> Prop) (u : A -> Prop) (f : A -> B) (g : type686 A) (h1 : term0 A B) : term8 A B s u f g.
Proof. exact (EQ_MP (@lem3556773 A B s u f g) (@lem3556772 A B s f g u h1)). Qed.
Lemma lem3556775 {A B : Type'} (g : type686 A) (s : A -> Prop) (u : A -> Prop) (f : A -> B) (h1 : term9 A B g s u f) : term9 A B g s u f.
Proof. exact (h1). Qed.
Lemma lem3556776 {A B : Type'} (g : type686 A) (s : A -> Prop) (u : A -> Prop) (f : A -> B) (h1 : term0 A B) (h2 : term9 A B g s u f) : (term10 A B f g) = (term11 A B f g).
Proof. exact (@lem3556774 A B s u f g h1 (@lem3556775 A B g s u f h2)). Qed.
Lemma lem3556777 {A B : Type'} (g : type686 A) (s : A -> Prop) (u : A -> Prop) (f : A -> B) (h1 : term9 A B g s u f) : term12 A B f g.
Proof. exact (fun h0 : term0 A B => @lem3556776 A B g s u f h0 h1). Qed.
Lemma lem3556778 {A B : Type'} (g : type686 A) (s : A -> Prop) (f : A -> B) (h1 : term13 A B g s f) : term13 A B g s f.
Proof. exact (h1). Qed.
Lemma lem3556779 {A B : Type'} (g : type686 A) (s : A -> Prop) (f : A -> B) (h1 : term13 A B g s f) : term12 A B f g.
Proof. exact (ex_elim (@lem3556778 A B g s f h1) (fun u : A -> Prop => fun h0 : term14 A B g s f u => @lem3556777 A B g s u f h0)). Qed.
Lemma lem3556780 {A B : Type'} (g : type686 A) (f : A -> B) (h1 : term15 A B g f) : term15 A B g f.
Proof. exact (h1). Qed.
Lemma lem3556781 {A B : Type'} (g : type686 A) (f : A -> B) (h1 : term15 A B g f) : term12 A B f g.
Proof. exact (ex_elim (@lem3556780 A B g f h1) (fun s : A -> Prop => fun h0 : term16 A B g f s => @lem3556779 A B g s f h0)). Qed.
Lemma lem3556782 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem3556783 {A B : Type'} (g : type686 A) (f : A -> B) (h1 : term0 A B) (h2 : term15 A B g f) : (term10 A B f g) = (term11 A B f g).
Proof. exact (@lem3556781 A B g f h2 (@lem3556782 A B h1)). Qed.
Lemma lem3556784 {A B : Type'} (f : A -> B) (g : type686 A) (h1 : term0 A B) : term17 A B f g.
Proof. exact (fun h0 : term15 A B g f => @lem3556783 A B g f h1 h0). Qed.
Lemma lem3556785 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term18 A B f.
Proof. exact (fun g : type686 A => @lem3556784 A B f g h1). Qed.
Lemma lem3556786 {A B : Type'} (h1 : term0 A B) : term19 A B.
Proof. exact (fun f : A -> B => @lem3556785 A B f h1). Qed.
Lemma lem3556787 {A B : Type'} : term20 A B.
Proof. exact (fun h0 : term0 A B => @lem3556786 A B h0). Qed.
Lemma lem3556788 {A B : Type'} : term19 A B.
Proof. exact (@lem3556787 A B (@lem3552877 A B)). Qed.
Lemma lem3556789 {A B : Type'} (f : A -> B) : term21 A B f.
Proof. exact (@lem3556788 A B f). Qed.
Lemma lem3556790 {A B : Type'} (f : A -> B) : (term21 A B f) = (term18 A B f).
Proof. exact (eq_refl (term21 A B f)). Qed.
Lemma lem3556791 {A B : Type'} (f : A -> B) : term18 A B f.
Proof. exact (EQ_MP (@lem3556790 A B f) (@lem3556789 A B f)). Qed.
Lemma lem3556792 {A B : Type'} (f : A -> B) (g : type686 A) : term22 A B f g.
Proof. exact (@lem3556791 A B f g). Qed.
Lemma lem3556793 {A B : Type'} (f : A -> B) (g : type686 A) : (term22 A B f g) = (term17 A B f g).
Proof. exact (eq_refl (term22 A B f g)). Qed.
Lemma lem3556795 {A B : Type'} (g : type686 A) (s : A -> Prop) (f : A -> B) (h1 : term23 A B g s f) : term23 A B g s f.
Proof. exact (h1). Qed.
Lemma lem3556796 {A B : Type'} (g : type686 A) (s : A -> Prop) (f : A -> B) (h1 : term24 A B g s f) : term24 A B g s f.
Proof. exact (h1). Qed.
Lemma lem3556797 {A : Type'} (g : type686 A) (h1 : term25 A g) : term25 A g.
Proof. exact (h1). Qed.
Lemma lem3556799 {A B : Type'} (f : A -> B) (g : type686 A) : term17 A B f g.
Proof. exact (EQ_MP (@lem3556793 A B f g) (@lem3556792 A B f g)). Qed.
Lemma lem3556800 {A B : Type'} (f : A -> B) (g : type686 A) : term17 A B f g.
Proof. exact (@lem3556799 A B f g). Qed.
Lemma lem3556801 {A : Type'} (s : A -> Prop) : term26 A s.
Proof. exact (@lem3220196 A s). Qed.
Lemma lem3556802 {A : Type'} (s : A -> Prop) : (term26 A s) = (@SUBSET A s (@UNIV A)).
Proof. exact (eq_refl (term26 A s)). Qed.
Lemma lem3556803 {A : Type'} (s : A -> Prop) : @SUBSET A s (@UNIV A).
Proof. exact (EQ_MP (@lem3556802 A s) (@lem3556801 A s)). Qed.
Lemma lem3556804 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@UNIV A)) = ((@SUBSET A s (@UNIV A)) = True).
Proof. exact (@lem7 (@SUBSET A s (@UNIV A))). Qed.
Lemma lem3556806 {A : Type'} (x : A) : term27 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem3556807 {A : Type'} (x : A) : (term27 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term27 A x)). Qed.
Lemma lem3556808 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem3556807 A x) (@lem3556806 A x)). Qed.
Lemma lem3556809 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem3556811 {A : Type'} (g : type686 A) : term28 A g.
Proof. exact (@lem82 (g = (@EMPTY (A -> Prop)))). Qed.
Lemma lem3556824 {A B : Type'} (t : A -> Prop) (g : type686 A) (s : A -> Prop) (f : A -> B) (h1 : term24 A B g s f) : term29 A B g s f t.
Proof. exact (@lem3556796 A B g s f h1 t). Qed.
Lemma lem3556825 {A B : Type'} (g : type686 A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term29 A B g s f t) = (term30 A B g s f t).
Proof. exact (eq_refl (term29 A B g s f t)). Qed.
Lemma lem3556826 {A B : Type'} (t : A -> Prop) (g : type686 A) (s : A -> Prop) (f : A -> B) (h1 : term24 A B g s f) : term30 A B g s f t.
Proof. exact (EQ_MP (@lem3556825 A B g s f t) (@lem3556824 A B t g s f h1)). Qed.
Lemma lem3556827 {A B : Type'} (g : type686 A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term30 A B g s f t) = ((term30 A B g s f t) = True).
Proof. exact (@lem7 (term30 A B g s f t)). Qed.
Lemma lem3556832 {A : Type'} (g : type686 A) (h1 : term25 A g) : (g = (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem3556811 A g (@lem3556797 A g h1)). Qed.
Lemma lem3556833 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3556834 {A : Type'} (g : type686 A) (h1 : term25 A g) : (term25 A g) = (~ False).
Proof. exact (MK_COMB (@lem3556833) (@lem3556832 A g h1)). Qed.
Lemma lem3556836 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3556837 {A : Type'} (g : type686 A) (h1 : term25 A g) : (term25 A g) = True.
Proof. exact (TRANS (@lem3556834 A g h1) (@lem3556836)). Qed.
Lemma lem3556838 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3556839 {A : Type'} (g : type686 A) (h1 : term25 A g) : (term31 A g) = (and True).
Proof. exact (MK_COMB (@lem3556838) (@lem3556837 A g h1)). Qed.
Lemma lem3556849 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3556804 A s) (@lem3556803 A s)). Qed.
Lemma lem3556850 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@UNIV A)) = True.
Proof. exact (@lem3556849 A s). Qed.
Lemma lem3556851 {A : Type'} (t : A -> Prop) : (@SUBSET A t (@UNIV A)) = True.
Proof. exact (@lem3556850 A t). Qed.
Lemma lem3556852 {A : Type'} (t : A -> Prop) (g : type686 A) : (term32 A t g) = (term32 A t g).
Proof. exact (eq_refl (term32 A t g)). Qed.
Lemma lem3556853 {A : Type'} (t : A -> Prop) (g : type686 A) : (term33 A g t) = (term34 A t g).
Proof. exact (MK_COMB (@lem3556852 A t g) (@lem3556851 A t)). Qed.
Lemma lem3556855 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3556856 {A : Type'} (t : A -> Prop) (g : type686 A) : (term34 A t g) = True.
Proof. exact (@lem3556855 (@IN (A -> Prop) t g)). Qed.
Lemma lem3556857 {A : Type'} (g : type686 A) (t : A -> Prop) : (term33 A g t) = True.
Proof. exact (TRANS (@lem3556853 A t g) (@lem3556856 A t g)). Qed.
Lemma lem3556858 {A : Type'} (g : type686 A) : (term35 A g) = (term36 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3556857 A g t)). Qed.
Lemma lem3556859 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3556860 {A : Type'} (g : type686 A) : (term37 A g) = (term38 A).
Proof. exact (MK_COMB (@lem3556859 A) (@lem3556858 A g)). Qed.
Lemma lem3556862 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3556863 {A : Type'} (t : Prop) : (term40 A t) = t.
Proof. exact (@lem3556862 (A -> Prop) t). Qed.
Lemma lem3556864 {A : Type'} : (term38 A) = True.
Proof. exact (@lem3556863 A True). Qed.
Lemma lem3556865 {A : Type'} (g : type686 A) : (term37 A g) = True.
Proof. exact (TRANS (@lem3556860 A g) (@lem3556864 A)). Qed.
Lemma lem3556866 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3556867 {A : Type'} (g : type686 A) : (term41 A g) = (and True).
Proof. exact (MK_COMB (@lem3556866) (@lem3556865 A g)). Qed.
Lemma lem3556881 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3556809 A x) (@lem3556808 A x)). Qed.
Lemma lem3556882 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3556881 A x). Qed.
Lemma lem3556883 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3556884 {A : Type'} (x : A) : (term42 A x) = (and True).
Proof. exact (MK_COMB (@lem3556883) (@lem3556882 A x)). Qed.
Lemma lem3556885 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term43 A B x f t) = (term43 A B x f t).
Proof. exact (eq_refl (term43 A B x f t)). Qed.
Lemma lem3556886 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term44 A B x f t) = (term45 A B x f t).
Proof. exact (MK_COMB (@lem3556884 A x) (@lem3556885 A B x f t)). Qed.
Lemma lem3556888 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3556889 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term45 A B x f t) = (term43 A B x f t).
Proof. exact (@lem3556888 (term43 A B x f t)). Qed.
Lemma lem3556890 {A B : Type'} (x : A) (f : A -> B) (t : A -> Prop) : (term44 A B x f t) = (term43 A B x f t).
Proof. exact (TRANS (@lem3556886 A B x f t) (@lem3556889 A B x f t)). Qed.
Lemma lem3556891 {A : Type'} (GEN_PVAR_85 : A) : (@SETSPEC A GEN_PVAR_85) = (@SETSPEC A GEN_PVAR_85).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_85)). Qed.
Lemma lem3556892 {A B : Type'} (GEN_PVAR_85 : A) (x : A) (f : A -> B) (t : A -> Prop) : (term46 A B GEN_PVAR_85 x f t) = (term47 A B GEN_PVAR_85 x f t).
Proof. exact (MK_COMB (@lem3556891 A GEN_PVAR_85) (@lem3556890 A B x f t)). Qed.
Lemma lem3556893 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3556894 {A B : Type'} (GEN_PVAR_85 : A) (f : A -> B) (t : A -> Prop) (x : A) : (term48 A B GEN_PVAR_85 f t x) = (term49 A B GEN_PVAR_85 f t x).
Proof. exact (MK_COMB (@lem3556892 A B GEN_PVAR_85 x f t) (@lem3556893 A x)). Qed.
Lemma lem3556895 {A B : Type'} (GEN_PVAR_85 : A) (f : A -> B) (t : A -> Prop) : (term50 A B GEN_PVAR_85 f t) = (term51 A B GEN_PVAR_85 f t).
Proof. exact (fun_ext (fun x : A => @lem3556894 A B GEN_PVAR_85 f t x)). Qed.
Lemma lem3556896 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3556897 {A B : Type'} (GEN_PVAR_85 : A) (f : A -> B) (t : A -> Prop) : (term52 A B GEN_PVAR_85 f t) = (term53 A B GEN_PVAR_85 f t).
Proof. exact (MK_COMB (@lem3556896 A) (@lem3556895 A B GEN_PVAR_85 f t)). Qed.
Lemma lem3556902 {A B : Type'} (f : A -> B) (t : A -> Prop) : (term54 A B f t) = (term55 A B f t).
Proof. exact (fun_ext (fun GEN_PVAR_85 : A => @lem3556897 A B GEN_PVAR_85 f t)). Qed.
Lemma lem3556903 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3556904 {A B : Type'} (f : A -> B) (t : A -> Prop) : (term56 A B f t) = (term57 A B f t).
Proof. exact (MK_COMB (@lem3556903 A) (@lem3556902 A B f t)). Qed.
Lemma lem3556905 {A : Type'} : (@SUBSET A) = (@SUBSET A).
Proof. exact (eq_refl (@SUBSET A)). Qed.
Lemma lem3556906 {A B : Type'} (f : A -> B) (t : A -> Prop) : (term58 A B f t) = (term59 A B f t).
Proof. exact (MK_COMB (@lem3556905 A) (@lem3556904 A B f t)). Qed.
Lemma lem3556907 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3556908 {A B : Type'} (f : A -> B) (t : A -> Prop) : (term60 A B f t) = (term61 A B f t).
Proof. exact (MK_COMB (@lem3556906 A B f t) (@lem3556907 A t)). Qed.
Lemma lem3556909 {A : Type'} (t : A -> Prop) (g : type686 A) (s : A -> Prop) : (term62 A t g s) = (term62 A t g s).
Proof. exact (eq_refl (term62 A t g s)). Qed.
Lemma lem3556910 {A B : Type'} (g : type686 A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term63 A B g s f t) = (term30 A B g s f t).
Proof. exact (MK_COMB (@lem3556909 A t g s) (@lem3556908 A B f t)). Qed.
Lemma lem3556912 {A B : Type'} (t : A -> Prop) (g : type686 A) (s : A -> Prop) (f : A -> B) (h1 : term24 A B g s f) : (term30 A B g s f t) = True.
Proof. exact (EQ_MP (@lem3556827 A B g s f t) (@lem3556826 A B t g s f h1)). Qed.
Lemma lem3556913 {A B : Type'} (t : A -> Prop) (g : type686 A) (s : A -> Prop) (f : A -> B) (h1 : term24 A B g s f) : (term30 A B g s f t) = True.
Proof. exact (@lem3556912 A B t g s f h1). Qed.
Lemma lem3556914 {A B : Type'} (t : A -> Prop) (g : type686 A) (s : A -> Prop) (f : A -> B) (h1 : term24 A B g s f) : (term63 A B g s f t) = True.
Proof. exact (TRANS (@lem3556910 A B g s f t) (@lem3556913 A B t g s f h1)). Qed.
Lemma lem3556915 {A B : Type'} (g : type686 A) (s : A -> Prop) (f : A -> B) (h1 : term24 A B g s f) : (term64 A B g s f) = (term36 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3556914 A B t g s f h1)). Qed.
Lemma lem3556916 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3556917 {A B : Type'} (g : type686 A) (s : A -> Prop) (f : A -> B) (h1 : term24 A B g s f) : (term65 A B g s f) = (term38 A).
Proof. exact (MK_COMB (@lem3556916 A) (@lem3556915 A B g s f h1)). Qed.
Lemma lem3556919 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3556920 {A : Type'} (t : Prop) : (term40 A t) = t.
Proof. exact (@lem3556919 (A -> Prop) t). Qed.
Lemma lem3556921 {A : Type'} : (term38 A) = True.
Proof. exact (@lem3556920 A True). Qed.
Lemma lem3556922 {A B : Type'} (g : type686 A) (s : A -> Prop) (f : A -> B) (h1 : term24 A B g s f) : (term65 A B g s f) = True.
Proof. exact (TRANS (@lem3556917 A B g s f h1) (@lem3556921 A)). Qed.
Lemma lem3556923 {A B : Type'} (g : type686 A) (s : A -> Prop) (f : A -> B) (h1 : term24 A B g s f) : (term66 A B g s f) = (True /\ True).
Proof. exact (MK_COMB (@lem3556867 A g) (@lem3556922 A B g s f h1)). Qed.
Lemma lem3556925 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3556926 : (True /\ True) = True.
Proof. exact (@lem3556925 True). Qed.
Lemma lem3556927 {A B : Type'} (g : type686 A) (s : A -> Prop) (f : A -> B) (h1 : term24 A B g s f) : (term66 A B g s f) = True.
Proof. exact (TRANS (@lem3556923 A B g s f h1) (@lem3556926)). Qed.
Lemma lem3556928 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : type686 A) (h1 : term24 A B g s f) (h2 : term25 A g) : (term67 A B g s f) = (True /\ True).
Proof. exact (MK_COMB (@lem3556839 A g h2) (@lem3556927 A B g s f h1)). Qed.
Lemma lem3556930 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3556931 : (True /\ True) = True.
Proof. exact (@lem3556930 True). Qed.
Lemma lem3556932 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : type686 A) (h1 : term24 A B g s f) (h2 : term25 A g) : (term67 A B g s f) = True.
Proof. exact (TRANS (@lem3556928 A B s f g h1 h2) (@lem3556931)). Qed.
Lemma lem3556933 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : type686 A) (h1 : term24 A B g s f) (h2 : term25 A g) : True = (term67 A B g s f).
Proof. exact (SYM (@lem3556932 A B s f g h1 h2)). Qed.
Lemma lem3556934 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : type686 A) (h1 : term24 A B g s f) (h2 : term25 A g) : term67 A B g s f.
Proof. exact (EQ_MP (@lem3556933 A B s f g h1 h2) (@lem0)). Qed.
Lemma lem3556935 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : type686 A) (h1 : term24 A B g s f) (h2 : term25 A g) : term13 A B g s f.
Proof. exact (ex_intro (term14 A B g s f) (@UNIV A) (@lem3556934 A B s f g h1 h2)). Qed.
Lemma lem3556936 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : type686 A) (h1 : term24 A B g s f) (h2 : term25 A g) : term15 A B g f.
Proof. exact (ex_intro (term16 A B g f) s (@lem3556935 A B s f g h1 h2)). Qed.
Lemma lem3556937 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : type686 A) (h1 : term24 A B g s f) (h2 : term25 A g) : (term10 A B f g) = (term11 A B f g).
Proof. exact (@lem3556800 A B f g (@lem3556936 A B s f g h1 h2)). Qed.
Lemma lem3556938 {A B : Type'} (g : type686 A) (s : A -> Prop) (f : A -> B) (h1 : term23 A B g s f) : term24 A B g s f.
Proof. exact (proj2 (@lem3556795 A B g s f h1)). Qed.
Lemma lem3556939 {A B : Type'} (g : type686 A) (s : A -> Prop) (f : A -> B) (h1 : term23 A B g s f) : term25 A g.
Proof. exact (proj1 (@lem3556795 A B g s f h1)). Qed.
Lemma lem3556940 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : type686 A) (h1 : term24 A B g s f) (h2 : term25 A g) : (term24 A B g s f) = ((term10 A B f g) = (term11 A B f g)).
Proof. exact (prop_ext (fun h3 : term24 A B g s f => @lem3556937 A B s f g h1 h2) (fun h3 : (term10 A B f g) = (term11 A B f g) => @lem3556796 A B g s f h1)). Qed.
Lemma lem3556941 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : type686 A) (h1 : term24 A B g s f) (h2 : term25 A g) : (term10 A B f g) = (term11 A B f g).
Proof. exact (EQ_MP (@lem3556940 A B s f g h1 h2) (@lem3556796 A B g s f h1)). Qed.
Lemma lem3556942 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : type686 A) (h1 : term24 A B g s f) (h2 : term25 A g) : (term25 A g) = ((term10 A B f g) = (term11 A B f g)).
Proof. exact (prop_ext (fun h3 : term25 A g => @lem3556941 A B s f g h1 h2) (fun h3 : (term10 A B f g) = (term11 A B f g) => @lem3556797 A g h2)). Qed.
Lemma lem3556943 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : type686 A) (h1 : term24 A B g s f) (h2 : term25 A g) : (term10 A B f g) = (term11 A B f g).
Proof. exact (EQ_MP (@lem3556942 A B s f g h1 h2) (@lem3556797 A g h2)). Qed.
Lemma lem3556944 {A B : Type'} (g : type686 A) (s : A -> Prop) (f : A -> B) (h1 : term25 A g) (h2 : term23 A B g s f) : (term24 A B g s f) = ((term10 A B f g) = (term11 A B f g)).
Proof. exact (prop_ext (fun h3 : term24 A B g s f => @lem3556943 A B s f g h3 h1) (fun h3 : (term10 A B f g) = (term11 A B f g) => @lem3556938 A B g s f h2)). Qed.
Lemma lem3556945 {A B : Type'} (g : type686 A) (s : A -> Prop) (f : A -> B) (h1 : term25 A g) (h2 : term23 A B g s f) : (term10 A B f g) = (term11 A B f g).
Proof. exact (EQ_MP (@lem3556944 A B g s f h1 h2) (@lem3556938 A B g s f h2)). Qed.
Lemma lem3556946 {A B : Type'} (g : type686 A) (s : A -> Prop) (f : A -> B) (h1 : term23 A B g s f) : (term25 A g) = ((term10 A B f g) = (term11 A B f g)).
Proof. exact (prop_ext (fun h2 : term25 A g => @lem3556945 A B g s f h2 h1) (fun h2 : (term10 A B f g) = (term11 A B f g) => @lem3556939 A B g s f h1)). Qed.
Lemma lem3556947 {A B : Type'} (g : type686 A) (s : A -> Prop) (f : A -> B) (h1 : term23 A B g s f) : (term10 A B f g) = (term11 A B f g).
Proof. exact (EQ_MP (@lem3556946 A B g s f h1) (@lem3556939 A B g s f h1)). Qed.
Lemma lem3556948 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : type686 A) : term68 A B s f g.
Proof. exact (fun h0 : term23 A B g s f => @lem3556947 A B g s f h0). Qed.
Lemma lem3556953 {A B : Type'} (f : A -> B) (g : type686 A) : term69 A B f g.
Proof. exact (fun s : A -> Prop => @lem3556948 A B s f g). Qed.
Lemma lem3556958 {A B : Type'} (f : A -> B) : term70 A B f.
Proof. exact (fun g : type686 A => @lem3556953 A B f g). Qed.
Lemma lem3556963 {A B : Type'} : term71 A B.
Proof. exact (fun f : A -> B => @lem3556958 A B f). Qed.
