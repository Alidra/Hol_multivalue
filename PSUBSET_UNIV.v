Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PSUBSET_UNIV_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1856_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211744_spec.
Require Import thm3211745_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3228775 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211745 A s t) (@lem3211744 A s t)). Qed.
Lemma lem3228776 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term0 A s t).
Proof. exact (@lem3228775 A s t). Qed.
Lemma lem3228777 {A : Type'} (s : A -> Prop) : (@PSUBSET A s (@UNIV A)) = (term1 A s).
Proof. exact (@lem3228776 A s (@UNIV A)). Qed.
Lemma lem3228781 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term2 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3228782 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term2 A s t).
Proof. exact (@lem3228781 A s t). Qed.
Lemma lem3228783 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@UNIV A)) = (term3 A s).
Proof. exact (@lem3228782 A s (@UNIV A)). Qed.
Lemma lem3228790 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3228791 {A : Type'} (s : A -> Prop) : (term4 A s) = (term5 A s).
Proof. exact (MK_COMB (@lem3228790) (@lem3228783 A s)). Qed.
Lemma lem3228795 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term6 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3228796 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term6 A s t).
Proof. exact (@lem3228795 A s t). Qed.
Lemma lem3228797 {A : Type'} (s : A -> Prop) : (s = (@UNIV A)) = (term7 A s).
Proof. exact (@lem3228796 A s (@UNIV A)). Qed.
Lemma lem3228806 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3228807 {A : Type'} (s : A -> Prop) : (term8 A s) = (term9 A s).
Proof. exact (MK_COMB (@lem3228806) (@lem3228797 A s)). Qed.
Lemma lem3228808 {A : Type'} (s : A -> Prop) : (term1 A s) = (term10 A s).
Proof. exact (MK_COMB (@lem3228791 A s) (@lem3228807 A s)). Qed.
Lemma lem3228811 {A : Type'} (s : A -> Prop) : (@PSUBSET A s (@UNIV A)) = (term10 A s).
Proof. exact (TRANS (@lem3228777 A s) (@lem3228808 A s)). Qed.
Lemma lem3228812 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3228813 {A : Type'} (s : A -> Prop) : (term11 A s) = (term12 A s).
Proof. exact (MK_COMB (@lem3228812) (@lem3228811 A s)). Qed.
Lemma lem3228818 {A : Type'} (s : A -> Prop) : (term13 A s) = (term13 A s).
Proof. exact (eq_refl (term13 A s)). Qed.
Lemma lem3228819 {A : Type'} (s : A -> Prop) : ((@PSUBSET A s (@UNIV A)) = (term13 A s)) = ((term10 A s) = (term13 A s)).
Proof. exact (MK_COMB (@lem3228813 A s) (@lem3228818 A s)). Qed.
Lemma lem3228824 {A : Type'} : (term14 A) = (term15 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3228819 A s)). Qed.
Lemma lem3228825 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3228826 {A : Type'} : (term16 A) = (term17 A).
Proof. exact (MK_COMB (@lem3228825 A) (@lem3228824 A)). Qed.
Lemma lem3228831 {A : Type'} : (term17 A) = (term16 A).
Proof. exact (SYM (@lem3228826 A)). Qed.
Lemma lem3228847 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3228848 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3228847 A P x). Qed.
Lemma lem3228849 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3228848 A s x). Qed.
Lemma lem3228850 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3228851 {A : Type'} (s : A -> Prop) (x : A) : (term18 A x s) = (term19 A s x).
Proof. exact (MK_COMB (@lem3228850) (@lem3228849 A s x)). Qed.
Lemma lem3228853 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem3228854 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3228853 A x). Qed.
Lemma lem3228855 {A : Type'} (s : A -> Prop) (x : A) : (term20 A s x) = (term21 A s x).
Proof. exact (MK_COMB (@lem3228851 A s x) (@lem3228854 A x)). Qed.
Lemma lem3228857 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3228858 {A : Type'} (s : A -> Prop) (x : A) : (term21 A s x) = True.
Proof. exact (@lem3228857 (s x)). Qed.
Lemma lem3228859 {A : Type'} (s : A -> Prop) (x : A) : (term20 A s x) = True.
Proof. exact (TRANS (@lem3228855 A s x) (@lem3228858 A s x)). Qed.
Lemma lem3228860 {A : Type'} (s : A -> Prop) : (term22 A s) = (term23 A).
Proof. exact (fun_ext (fun x : A => @lem3228859 A s x)). Qed.
Lemma lem3228861 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3228862 {A : Type'} (s : A -> Prop) : (term3 A s) = (term24 A).
Proof. exact (MK_COMB (@lem3228861 A) (@lem3228860 A s)). Qed.
Lemma lem3228864 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3228865 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (@lem3228864 A t). Qed.
Lemma lem3228866 {A : Type'} : (term24 A) = True.
Proof. exact (@lem3228865 A True). Qed.
Lemma lem3228867 {A : Type'} (s : A -> Prop) : (term3 A s) = True.
Proof. exact (TRANS (@lem3228862 A s) (@lem3228866 A)). Qed.
Lemma lem3228868 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3228869 {A : Type'} (s : A -> Prop) : (term5 A s) = (and True).
Proof. exact (MK_COMB (@lem3228868) (@lem3228867 A s)). Qed.
Lemma lem3228877 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3228878 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3228877 A P x). Qed.
Lemma lem3228879 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3228878 A s x). Qed.
Lemma lem3228880 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3228881 {A : Type'} (s : A -> Prop) (x : A) : (term26 A x s) = (term27 A s x).
Proof. exact (MK_COMB (@lem3228880) (@lem3228879 A s x)). Qed.
Lemma lem3228883 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem3228884 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3228883 A x). Qed.
Lemma lem3228885 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x (@UNIV A))) = ((s x) = True).
Proof. exact (MK_COMB (@lem3228881 A s x) (@lem3228884 A x)). Qed.
Lemma lem3228887 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem3228888 {A : Type'} (s : A -> Prop) (x : A) : ((s x) = True) = (s x).
Proof. exact (@lem3228887 (s x)). Qed.
Lemma lem3228889 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x (@UNIV A))) = (s x).
Proof. exact (TRANS (@lem3228885 A s x) (@lem3228888 A s x)). Qed.
Lemma lem3228890 {A : Type'} (s : A -> Prop) : (term28 A s) = (term29 A s).
Proof. exact (fun_ext (fun x : A => @lem3228889 A s x)). Qed.
Lemma lem3228891 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3228892 {A : Type'} (s : A -> Prop) : (term7 A s) = (term30 A s).
Proof. exact (MK_COMB (@lem3228891 A) (@lem3228890 A s)). Qed.
Lemma lem3228897 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3228898 {A : Type'} (s : A -> Prop) : (term9 A s) = (term31 A s).
Proof. exact (MK_COMB (@lem3228897) (@lem3228892 A s)). Qed.
Lemma lem3228899 {A : Type'} (s : A -> Prop) : (term10 A s) = (term32 A s).
Proof. exact (MK_COMB (@lem3228869 A s) (@lem3228898 A s)). Qed.
Lemma lem3228901 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3228902 {A : Type'} (s : A -> Prop) : (term32 A s) = (term31 A s).
Proof. exact (@lem3228901 (term31 A s)). Qed.
Lemma lem3228907 {A : Type'} (s : A -> Prop) : (term10 A s) = (term31 A s).
Proof. exact (TRANS (@lem3228899 A s) (@lem3228902 A s)). Qed.
Lemma lem3228908 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3228909 {A : Type'} (s : A -> Prop) : (term12 A s) = (term33 A s).
Proof. exact (MK_COMB (@lem3228908) (@lem3228907 A s)). Qed.
Lemma lem3228915 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3228916 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3228915 A P x). Qed.
Lemma lem3228917 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3228916 A s x). Qed.
Lemma lem3228918 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3228919 {A : Type'} (s : A -> Prop) (x : A) : (term34 A x s) = (term35 A s x).
Proof. exact (MK_COMB (@lem3228918) (@lem3228917 A s x)). Qed.
Lemma lem3228920 {A : Type'} (s : A -> Prop) : (term36 A s) = (term37 A s).
Proof. exact (fun_ext (fun x : A => @lem3228919 A s x)). Qed.
Lemma lem3228921 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3228922 {A : Type'} (s : A -> Prop) : (term13 A s) = (term38 A s).
Proof. exact (MK_COMB (@lem3228921 A) (@lem3228920 A s)). Qed.
Lemma lem3228927 {A : Type'} (s : A -> Prop) : ((term10 A s) = (term13 A s)) = ((term31 A s) = (term38 A s)).
Proof. exact (MK_COMB (@lem3228909 A s) (@lem3228922 A s)). Qed.
Lemma lem3228930 {A : Type'} : (term15 A) = (term39 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3228927 A s)). Qed.
Lemma lem3228931 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3228932 {A : Type'} : (term17 A) = (term40 A).
Proof. exact (MK_COMB (@lem3228931 A) (@lem3228930 A)). Qed.
Lemma lem3228937 {A : Type'} : (term40 A) = (term17 A).
Proof. exact (SYM (@lem3228932 A)). Qed.
Lemma lem3228939 (p : Prop) : p = (term41 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3228940 {A : Type'} : (term40 A) = (term42 A).
Proof. exact (@lem3228939 (term40 A)). Qed.
Lemma lem3228941 {A : Type'} : (term42 A) = (term40 A).
Proof. exact (SYM (@lem3228940 A)). Qed.
Lemma lem3228942 {A : Type'} (h1 : term43 A) : term43 A.
Proof. exact (h1). Qed.
Lemma lem3228945 {A : Type'} (h1 : term42 A) : term42 A.
Proof. exact (h1). Qed.
Lemma lem3228946 {A : Type'} : term44 A.
Proof. exact (fun h0 : term42 A => @lem3228945 A h0). Qed.
Lemma lem3228947 {A : Type'} (h1 : term44 A) : term44 A.
Proof. exact (h1). Qed.
Lemma lem3228948 {A : Type'} (h1 : term42 A) : term42 A.
Proof. exact (h1). Qed.
Lemma lem3228949 {A : Type'} (h1 : term42 A) (h2 : term44 A) : term42 A.
Proof. exact (@lem3228947 A h2 (@lem3228948 A h1)). Qed.
Lemma lem3228950 {A : Type'} (h1 : term42 A) : term45 A.
Proof. exact (fun h0 : term44 A => @lem3228949 A h1 h0). Qed.
Lemma lem3228951 {A : Type'} (h1 : term44 A) : term44 A.
Proof. exact (h1). Qed.
Lemma lem3228952 {A : Type'} (h1 : term42 A) (h2 : term44 A) : term42 A.
Proof. exact (@lem3228950 A h1 (@lem3228951 A h2)). Qed.
Lemma lem3228953 {A : Type'} (h1 : term44 A) : term44 A.
Proof. exact (fun h0 : term42 A => @lem3228952 A h0 h1). Qed.
Lemma lem3228954 {A : Type'} : term46 A.
Proof. exact (fun h0 : term44 A => @lem3228953 A h0). Qed.
Lemma lem3228957 {A : Type'} : term44 A.
Proof. exact (@lem3228954 A (@lem3228946 A)). Qed.
Lemma lem3228958 {A : Type'} : term44 A.
Proof. exact (@lem3228957 A). Qed.
Lemma lem3228960 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3228961 {A : Type'} : (term42 A) = (term47 A).
Proof. exact (@lem3228960 (term43 A)). Qed.
Lemma lem3228963 (t : Prop) : (term48 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3228964 {A : Type'} : (term47 A) = (term40 A).
Proof. exact (@lem3228963 (term40 A)). Qed.
Lemma lem3228981 {A : Type'} : (term42 A) = (term40 A).
Proof. exact (TRANS (@lem3228961 A) (@lem3228964 A)). Qed.
Lemma lem3228984 {A : Type'} (s : A -> Prop) (x : A) : (term35 A s x) = (term35 A s x).
Proof. exact (eq_refl (term35 A s x)). Qed.
Lemma lem3228985 {A : Type'} (s : A -> Prop) : (term37 A s) = (term37 A s).
Proof. exact (fun_ext (fun x : A => @lem3228984 A s x)). Qed.
Lemma lem3228986 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3228987 {A : Type'} (s : A -> Prop) : (term38 A s) = (term38 A s).
Proof. exact (MK_COMB (@lem3228986 A) (@lem3228985 A s)). Qed.
Lemma lem3228988 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3228989 {A : Type'} (s : A -> Prop) : (term29 A s) = (term29 A s).
Proof. exact (fun_ext (fun x : A => @lem3228988 A s x)). Qed.
Lemma lem3228990 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3228991 {A : Type'} (s : A -> Prop) : (term30 A s) = (term30 A s).
Proof. exact (MK_COMB (@lem3228990 A) (@lem3228989 A s)). Qed.
Lemma lem3228992 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3228993 {A : Type'} (s : A -> Prop) : (term31 A s) = (term31 A s).
Proof. exact (MK_COMB (@lem3228992) (@lem3228991 A s)). Qed.
Lemma lem3228994 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3228995 {A : Type'} (s : A -> Prop) : (term33 A s) = (term33 A s).
Proof. exact (MK_COMB (@lem3228994) (@lem3228993 A s)). Qed.
Lemma lem3228996 {A : Type'} (s : A -> Prop) : ((term31 A s) = (term38 A s)) = ((term31 A s) = (term38 A s)).
Proof. exact (MK_COMB (@lem3228995 A s) (@lem3228987 A s)). Qed.
Lemma lem3228997 {A : Type'} : (term39 A) = (term39 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3228996 A s)). Qed.
Lemma lem3228998 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3228999 {A : Type'} : (term40 A) = (term40 A).
Proof. exact (MK_COMB (@lem3228998 A) (@lem3228997 A)). Qed.
Lemma lem3229020 {A : Type'} : (term42 A) = (term40 A).
Proof. exact (TRANS (@lem3228981 A) (@lem3228999 A)). Qed.
Lemma lem3229021 {A : Type'} : (term40 A) = (term42 A).
Proof. exact (SYM (@lem3229020 A)). Qed.
Lemma lem3229023 (p : Prop) : p = (term41 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3229024 {A : Type'} (s : A -> Prop) : ((term31 A s) = (term38 A s)) = (term49 A s).
Proof. exact (@lem3229023 ((term31 A s) = (term38 A s))). Qed.
Lemma lem3229025 {A : Type'} (s : A -> Prop) : (term49 A s) = ((term31 A s) = (term38 A s)).
Proof. exact (SYM (@lem3229024 A s)). Qed.
Lemma lem3229026 {A : Type'} (s : A -> Prop) (h1 : term50 A s) : term50 A s.
Proof. exact (h1). Qed.
Lemma lem3229028 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3229029 {A : Type'} (P : A -> Prop) : (term51 A P) = (term38 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3229030 {A : Type'} (s : A -> Prop) : (term31 A s) = (term52 A s).
Proof. exact (@lem3229029 A (term29 A s)). Qed.
Lemma lem3229031 {A : Type'} (s : A -> Prop) (x : A) : (term53 A s x) = (s x).
Proof. exact (eq_refl (term53 A s x)). Qed.
Lemma lem3229032 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3229034 {A : Type'} (s : A -> Prop) (x : A) : (term54 A s x) = (term35 A s x).
Proof. exact (MK_COMB (@lem3229032) (@lem3229031 A s x)). Qed.
Lemma lem3229035 {A : Type'} (s : A -> Prop) : (term55 A s) = (term37 A s).
Proof. exact (fun_ext (fun x : A => @lem3229034 A s x)). Qed.
Lemma lem3229036 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3229037 {A : Type'} (s : A -> Prop) : (term52 A s) = (term38 A s).
Proof. exact (MK_COMB (@lem3229036 A) (@lem3229035 A s)). Qed.
Lemma lem3229038 {A : Type'} (s : A -> Prop) : (term31 A s) = (term38 A s).
Proof. exact (TRANS (@lem3229030 A s) (@lem3229037 A s)). Qed.
Lemma lem3229039 {A : Type'} (s : A -> Prop) : (term29 A s) = (term29 A s).
Proof. exact (fun_ext (fun x : A => @lem3229028 A s x)). Qed.
Lemma lem3229040 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3229041 {A : Type'} (s : A -> Prop) : (term30 A s) = (term30 A s).
Proof. exact (MK_COMB (@lem3229040 A) (@lem3229039 A s)). Qed.
Lemma lem3229042 {A : Type'} (s : A -> Prop) : (term56 A s) = (term30 A s).
Proof. exact (@lem16933 (term30 A s)). Qed.
Lemma lem3229043 {A : Type'} (s : A -> Prop) : (term56 A s) = (term30 A s).
Proof. exact (TRANS (@lem3229042 A s) (@lem3229041 A s)). Qed.
Lemma lem3229044 {A : Type'} (s : A -> Prop) (x : A) : (term35 A s x) = (term35 A s x).
Proof. exact (eq_refl (term35 A s x)). Qed.
Lemma lem3229047 {A : Type'} (s : A -> Prop) (x : A) : (term57 A s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem3229048 {A : Type'} (P : A -> Prop) : (term58 A P) = (term59 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3229049 {A : Type'} (s : A -> Prop) : (term60 A s) = (term61 A s).
Proof. exact (@lem3229048 A (term37 A s)). Qed.
Lemma lem3229050 {A : Type'} (s : A -> Prop) (x : A) : (term62 A s x) = (term35 A s x).
Proof. exact (eq_refl (term62 A s x)). Qed.
Lemma lem3229051 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3229052 {A : Type'} (s : A -> Prop) (x : A) : (term63 A s x) = (term57 A s x).
Proof. exact (MK_COMB (@lem3229051) (@lem3229050 A s x)). Qed.
Lemma lem3229053 {A : Type'} (s : A -> Prop) (x : A) : (term63 A s x) = (s x).
Proof. exact (TRANS (@lem3229052 A s x) (@lem3229047 A s x)). Qed.
Lemma lem3229054 {A : Type'} (s : A -> Prop) : (term64 A s) = (term29 A s).
Proof. exact (fun_ext (fun x : A => @lem3229053 A s x)). Qed.
Lemma lem3229055 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3229056 {A : Type'} (s : A -> Prop) : (term61 A s) = (term30 A s).
Proof. exact (MK_COMB (@lem3229055 A) (@lem3229054 A s)). Qed.
Lemma lem3229057 {A : Type'} (s : A -> Prop) : (term60 A s) = (term30 A s).
Proof. exact (TRANS (@lem3229049 A s) (@lem3229056 A s)). Qed.
Lemma lem3229058 {A : Type'} (s : A -> Prop) : (term37 A s) = (term37 A s).
Proof. exact (fun_ext (fun x : A => @lem3229044 A s x)). Qed.
Lemma lem3229059 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3229060 {A : Type'} (s : A -> Prop) : (term38 A s) = (term38 A s).
Proof. exact (MK_COMB (@lem3229059 A) (@lem3229058 A s)). Qed.
Lemma lem3229061 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3229062 {A : Type'} (s : A -> Prop) : (term65 A s) = (term66 A s).
Proof. exact (MK_COMB (@lem3229061) (@lem3229043 A s)). Qed.
Lemma lem3229063 {A : Type'} (s : A -> Prop) : (term67 A s) = (term68 A s).
Proof. exact (MK_COMB (@lem3229062 A s) (@lem3229060 A s)). Qed.
Lemma lem3229064 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3229065 {A : Type'} (s : A -> Prop) : (term69 A s) = (term70 A s).
Proof. exact (MK_COMB (@lem3229064) (@lem3229038 A s)). Qed.
Lemma lem3229066 {A : Type'} (s : A -> Prop) : (term71 A s) = (term72 A s).
Proof. exact (MK_COMB (@lem3229065 A s) (@lem3229057 A s)). Qed.
Lemma lem3229067 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3229068 {A : Type'} (s : A -> Prop) : (term73 A s) = (term74 A s).
Proof. exact (MK_COMB (@lem3229067) (@lem3229066 A s)). Qed.
Lemma lem3229069 {A : Type'} (s : A -> Prop) : (term75 A s) = (term76 A s).
Proof. exact (MK_COMB (@lem3229068 A s) (@lem3229063 A s)). Qed.
Lemma lem3229070 {A : Type'} (s : A -> Prop) : (term50 A s) = (term75 A s).
Proof. exact (@lem17646 (term31 A s) (term38 A s)). Qed.
Lemma lem3229071 {A : Type'} (s : A -> Prop) : (term50 A s) = (term76 A s).
Proof. exact (TRANS (@lem3229070 A s) (@lem3229069 A s)). Qed.
Lemma lem3229090 {A : Type'} (P : A -> Prop) (Q : Prop) : (term77 A P Q) = (term78 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3229091 {A : Type'} (P : A -> Prop) (Q : Prop) : (term77 A P Q) = (term78 A P Q).
Proof. exact (@lem3229090 A P Q). Qed.
Lemma lem3229092 {A : Type'} (s : A -> Prop) : (term79 A s) = (term80 A s).
Proof. exact (@lem3229091 A (term37 A s) (term30 A s)). Qed.
Lemma lem3229093 {A : Type'} (s : A -> Prop) (x : A) : (term62 A s x) = (term35 A s x).
Proof. exact (eq_refl (term62 A s x)). Qed.
Lemma lem3229094 {A : Type'} (s : A -> Prop) : (term81 A s) = (term37 A s).
Proof. exact (fun_ext (fun x : A => @lem3229093 A s x)). Qed.
Lemma lem3229095 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3229096 {A : Type'} (s : A -> Prop) : (term82 A s) = (term38 A s).
Proof. exact (MK_COMB (@lem3229095 A) (@lem3229094 A s)). Qed.
Lemma lem3229097 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3229098 {A : Type'} (s : A -> Prop) : (term83 A s) = (term70 A s).
Proof. exact (MK_COMB (@lem3229097) (@lem3229096 A s)). Qed.
Lemma lem3229099 {A : Type'} (s : A -> Prop) : (term30 A s) = (term30 A s).
Proof. exact (eq_refl (term30 A s)). Qed.
Lemma lem3229100 {A : Type'} (s : A -> Prop) : (term79 A s) = (term72 A s).
Proof. exact (MK_COMB (@lem3229098 A s) (@lem3229099 A s)). Qed.
Lemma lem3229101 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3229102 {A : Type'} (s : A -> Prop) : (term84 A s) = (term85 A s).
Proof. exact (MK_COMB (@lem3229101) (@lem3229100 A s)). Qed.
Lemma lem3229103 {A : Type'} (s : A -> Prop) (x : A) : (term62 A s x) = (term35 A s x).
Proof. exact (eq_refl (term62 A s x)). Qed.
Lemma lem3229104 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3229105 {A : Type'} (s : A -> Prop) (x : A) : (term86 A s x) = (term87 A s x).
Proof. exact (MK_COMB (@lem3229104) (@lem3229103 A s x)). Qed.
Lemma lem3229106 {A : Type'} (s : A -> Prop) : (term30 A s) = (term30 A s).
Proof. exact (eq_refl (term30 A s)). Qed.
Lemma lem3229107 {A : Type'} (x : A) (s : A -> Prop) : (term88 A x s) = (term89 A x s).
Proof. exact (MK_COMB (@lem3229105 A s x) (@lem3229106 A s)). Qed.
Lemma lem3229108 {A : Type'} (s : A -> Prop) : (term90 A s) = (term91 A s).
Proof. exact (fun_ext (fun x : A => @lem3229107 A x s)). Qed.
Lemma lem3229109 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3229110 {A : Type'} (s : A -> Prop) : (term80 A s) = (term92 A s).
Proof. exact (MK_COMB (@lem3229109 A) (@lem3229108 A s)). Qed.
Lemma lem3229111 {A : Type'} (s : A -> Prop) : ((term79 A s) = (term80 A s)) = ((term72 A s) = (term92 A s)).
Proof. exact (MK_COMB (@lem3229102 A s) (@lem3229110 A s)). Qed.
Lemma lem3229112 {A : Type'} (s : A -> Prop) : (term72 A s) = (term92 A s).
Proof. exact (EQ_MP (@lem3229111 A s) (@lem3229092 A s)). Qed.
Lemma lem3229113 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3229114 {A : Type'} (s : A -> Prop) : (term74 A s) = (term93 A s).
Proof. exact (MK_COMB (@lem3229113) (@lem3229112 A s)). Qed.
Lemma lem3229116 {A : Type'} (P : Prop) (Q : A -> Prop) : (term94 A P Q) = (term95 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3229117 {A : Type'} (P : Prop) (Q : A -> Prop) : (term94 A P Q) = (term95 A P Q).
Proof. exact (@lem3229116 A P Q). Qed.
Lemma lem3229118 {A : Type'} (s : A -> Prop) : (term96 A s) = (term97 A s).
Proof. exact (@lem3229117 A (term30 A s) (term37 A s)). Qed.
Lemma lem3229119 {A : Type'} (s : A -> Prop) (x : A) : (term62 A s x) = (term35 A s x).
Proof. exact (eq_refl (term62 A s x)). Qed.
Lemma lem3229120 {A : Type'} (s : A -> Prop) : (term81 A s) = (term37 A s).
Proof. exact (fun_ext (fun x : A => @lem3229119 A s x)). Qed.
Lemma lem3229121 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3229122 {A : Type'} (s : A -> Prop) : (term82 A s) = (term38 A s).
Proof. exact (MK_COMB (@lem3229121 A) (@lem3229120 A s)). Qed.
Lemma lem3229123 {A : Type'} (s : A -> Prop) : (term66 A s) = (term66 A s).
Proof. exact (eq_refl (term66 A s)). Qed.
Lemma lem3229124 {A : Type'} (s : A -> Prop) : (term96 A s) = (term68 A s).
Proof. exact (MK_COMB (@lem3229123 A s) (@lem3229122 A s)). Qed.
Lemma lem3229125 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3229126 {A : Type'} (s : A -> Prop) : (term98 A s) = (term99 A s).
Proof. exact (MK_COMB (@lem3229125) (@lem3229124 A s)). Qed.
Lemma lem3229127 {A : Type'} (s : A -> Prop) (x : A) : (term62 A s x) = (term35 A s x).
Proof. exact (eq_refl (term62 A s x)). Qed.
Lemma lem3229128 {A : Type'} (s : A -> Prop) : (term66 A s) = (term66 A s).
Proof. exact (eq_refl (term66 A s)). Qed.
Lemma lem3229129 {A : Type'} (s : A -> Prop) (x : A) : (term100 A s x) = (term101 A s x).
Proof. exact (MK_COMB (@lem3229128 A s) (@lem3229127 A s x)). Qed.
Lemma lem3229130 {A : Type'} (s : A -> Prop) : (term102 A s) = (term103 A s).
Proof. exact (fun_ext (fun x : A => @lem3229129 A s x)). Qed.
Lemma lem3229131 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3229132 {A : Type'} (s : A -> Prop) : (term97 A s) = (term104 A s).
Proof. exact (MK_COMB (@lem3229131 A) (@lem3229130 A s)). Qed.
Lemma lem3229133 {A : Type'} (s : A -> Prop) : ((term96 A s) = (term97 A s)) = ((term68 A s) = (term104 A s)).
Proof. exact (MK_COMB (@lem3229126 A s) (@lem3229132 A s)). Qed.
Lemma lem3229134 {A : Type'} (s : A -> Prop) : (term68 A s) = (term104 A s).
Proof. exact (EQ_MP (@lem3229133 A s) (@lem3229118 A s)). Qed.
Lemma lem3229135 {A : Type'} (s : A -> Prop) : (term76 A s) = (term105 A s).
Proof. exact (MK_COMB (@lem3229114 A s) (@lem3229134 A s)). Qed.
Lemma lem3229137 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term106 A P Q) = (term107 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3229138 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term106 A P Q) = (term107 A P Q).
Proof. exact (@lem3229137 A P Q). Qed.
Lemma lem3229139 {A : Type'} (s : A -> Prop) : (term108 A s) = (term109 A s).
Proof. exact (@lem3229138 A (term91 A s) (term103 A s)). Qed.
Lemma lem3229140 {A : Type'} (x : A) (s : A -> Prop) : (term110 A s x) = (term89 A x s).
Proof. exact (eq_refl (term110 A s x)). Qed.
Lemma lem3229141 {A : Type'} (s : A -> Prop) : (term111 A s) = (term91 A s).
Proof. exact (fun_ext (fun x : A => @lem3229140 A x s)). Qed.
Lemma lem3229142 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3229143 {A : Type'} (s : A -> Prop) : (term112 A s) = (term92 A s).
Proof. exact (MK_COMB (@lem3229142 A) (@lem3229141 A s)). Qed.
Lemma lem3229144 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3229145 {A : Type'} (s : A -> Prop) : (term113 A s) = (term93 A s).
Proof. exact (MK_COMB (@lem3229144) (@lem3229143 A s)). Qed.
Lemma lem3229146 {A : Type'} (s : A -> Prop) (x : A) : (term114 A s x) = (term101 A s x).
Proof. exact (eq_refl (term114 A s x)). Qed.
Lemma lem3229147 {A : Type'} (s : A -> Prop) : (term115 A s) = (term103 A s).
Proof. exact (fun_ext (fun x : A => @lem3229146 A s x)). Qed.
Lemma lem3229148 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3229149 {A : Type'} (s : A -> Prop) : (term116 A s) = (term104 A s).
Proof. exact (MK_COMB (@lem3229148 A) (@lem3229147 A s)). Qed.
Lemma lem3229150 {A : Type'} (s : A -> Prop) : (term108 A s) = (term105 A s).
Proof. exact (MK_COMB (@lem3229145 A s) (@lem3229149 A s)). Qed.
Lemma lem3229151 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3229152 {A : Type'} (s : A -> Prop) : (term117 A s) = (term118 A s).
Proof. exact (MK_COMB (@lem3229151) (@lem3229150 A s)). Qed.
Lemma lem3229153 {A : Type'} (x : A) (s : A -> Prop) : (term110 A s x) = (term89 A x s).
Proof. exact (eq_refl (term110 A s x)). Qed.
Lemma lem3229154 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3229155 {A : Type'} (x : A) (s : A -> Prop) : (term119 A s x) = (term120 A x s).
Proof. exact (MK_COMB (@lem3229154) (@lem3229153 A x s)). Qed.
Lemma lem3229156 {A : Type'} (s : A -> Prop) (x : A) : (term114 A s x) = (term101 A s x).
Proof. exact (eq_refl (term114 A s x)). Qed.
Lemma lem3229157 {A : Type'} (s : A -> Prop) (x : A) : (term121 A s x) = (term122 A s x).
Proof. exact (MK_COMB (@lem3229155 A x s) (@lem3229156 A s x)). Qed.
Lemma lem3229158 {A : Type'} (s : A -> Prop) : (term123 A s) = (term124 A s).
Proof. exact (fun_ext (fun x : A => @lem3229157 A s x)). Qed.
Lemma lem3229159 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3229160 {A : Type'} (s : A -> Prop) : (term109 A s) = (term125 A s).
Proof. exact (MK_COMB (@lem3229159 A) (@lem3229158 A s)). Qed.
Lemma lem3229161 {A : Type'} (s : A -> Prop) : ((term108 A s) = (term109 A s)) = ((term105 A s) = (term125 A s)).
Proof. exact (MK_COMB (@lem3229152 A s) (@lem3229160 A s)). Qed.
Lemma lem3229162 {A : Type'} (s : A -> Prop) : (term105 A s) = (term125 A s).
Proof. exact (EQ_MP (@lem3229161 A s) (@lem3229139 A s)). Qed.
Lemma lem3229164 {A : Type'} (s : A -> Prop) : (term76 A s) = (term125 A s).
Proof. exact (TRANS (@lem3229135 A s) (@lem3229162 A s)). Qed.
Lemma lem3229165 {A : Type'} (s : A -> Prop) : (term50 A s) = (term125 A s).
Proof. exact (TRANS (@lem3229071 A s) (@lem3229164 A s)). Qed.
Lemma lem3229166 {A : Type'} (s : A -> Prop) (h1 : term50 A s) : term125 A s.
Proof. exact (EQ_MP (@lem3229165 A s) (@lem3229026 A s h1)). Qed.
Lemma lem3229167 {A : Type'} (s : A -> Prop) (x : A) (h1 : term122 A s x) : term122 A s x.
Proof. exact (h1). Qed.
Lemma lem3229172 {A : Type'} (s : A -> Prop) (x : A) : (term35 A s x) = (term35 A s x).
Proof. exact (eq_refl (term35 A s x)). Qed.
Lemma lem3229175 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3229176 {A : Type'} (s : A -> Prop) : (term29 A s) = (term29 A s).
Proof. exact (fun_ext (fun x : A => @lem3229175 A s x)). Qed.
Lemma lem3229177 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3229178 {A : Type'} (s : A -> Prop) : (term30 A s) = (term30 A s).
Proof. exact (MK_COMB (@lem3229177 A) (@lem3229176 A s)). Qed.
Lemma lem3229179 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3229180 {A : Type'} (s : A -> Prop) : (term66 A s) = (term66 A s).
Proof. exact (MK_COMB (@lem3229179) (@lem3229178 A s)). Qed.
Lemma lem3229181 {A : Type'} (s : A -> Prop) (x : A) : (term101 A s x) = (term101 A s x).
Proof. exact (MK_COMB (@lem3229180 A s) (@lem3229172 A s x)). Qed.
Lemma lem3229184 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3229185 {A : Type'} (s : A -> Prop) : (term29 A s) = (term29 A s).
Proof. exact (fun_ext (fun x : A => @lem3229184 A s x)). Qed.
Lemma lem3229186 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3229187 {A : Type'} (s : A -> Prop) : (term30 A s) = (term30 A s).
Proof. exact (MK_COMB (@lem3229186 A) (@lem3229185 A s)). Qed.
Lemma lem3229194 {A : Type'} (s : A -> Prop) (x : A) : (term87 A s x) = (term87 A s x).
Proof. exact (eq_refl (term87 A s x)). Qed.
Lemma lem3229195 {A : Type'} (x : A) (s : A -> Prop) : (term89 A x s) = (term89 A x s).
Proof. exact (MK_COMB (@lem3229194 A s x) (@lem3229187 A s)). Qed.
Lemma lem3229196 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3229197 {A : Type'} (x : A) (s : A -> Prop) : (term120 A x s) = (term120 A x s).
Proof. exact (MK_COMB (@lem3229196) (@lem3229195 A x s)). Qed.
Lemma lem3229198 {A : Type'} (s : A -> Prop) (x : A) : (term122 A s x) = (term122 A s x).
Proof. exact (MK_COMB (@lem3229197 A x s) (@lem3229181 A s x)). Qed.
Lemma lem3229199 {A : Type'} (s : A -> Prop) (x : A) (h1 : term122 A s x) : term122 A s x.
Proof. exact (EQ_MP (@lem3229198 A s x) (@lem3229167 A s x h1)). Qed.
Lemma lem3229200 {A : Type'} (x : A) (s : A -> Prop) (h1 : term89 A x s) : term89 A x s.
Proof. exact (h1). Qed.
Lemma lem3229201 {A : Type'} (s : A -> Prop) (x : A) (h1 : term101 A s x) : term101 A s x.
Proof. exact (h1). Qed.
Lemma lem3229202 {A : Type'} (x : A) (s : A -> Prop) (h1 : term89 A x s) : term30 A s.
Proof. exact (proj2 (@lem3229200 A x s h1)). Qed.
Lemma lem3229205 {A : Type'} (s : A -> Prop) (x : A) (h1 : term101 A s x) : term30 A s.
Proof. exact (proj1 (@lem3229201 A s x h1)). Qed.
Lemma lem3229211 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3229212 {A : Type'} (s : A -> Prop) : (term29 A s) = (term29 A s).
Proof. exact (fun_ext (fun x : A => @lem3229211 A s x)). Qed.
Lemma lem3229213 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3229215 {A : Type'} (s : A -> Prop) : (term30 A s) = (term30 A s).
Proof. exact (MK_COMB (@lem3229213 A) (@lem3229212 A s)). Qed.
Lemma lem3229216 {A : Type'} (x : A) (s : A -> Prop) (h1 : term89 A x s) : term30 A s.
Proof. exact (EQ_MP (@lem3229215 A s) (@lem3229202 A x s h1)). Qed.
Lemma lem3229218 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3229219 {A : Type'} (s : A -> Prop) : (term29 A s) = (term29 A s).
Proof. exact (fun_ext (fun x : A => @lem3229218 A s x)). Qed.
Lemma lem3229220 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3229222 {A : Type'} (s : A -> Prop) : (term30 A s) = (term30 A s).
Proof. exact (MK_COMB (@lem3229220 A) (@lem3229219 A s)). Qed.
Lemma lem3229223 {A : Type'} (s : A -> Prop) (x : A) (h1 : term101 A s x) : term30 A s.
Proof. exact (EQ_MP (@lem3229222 A s) (@lem3229205 A s x h1)). Qed.
Lemma lem3229228 {A : Type'} (_33177 : A) (x : A) (s : A -> Prop) (h1 : term89 A x s) : term53 A s _33177.
Proof. exact (@lem3229216 A x s h1 _33177). Qed.
Lemma lem3229229 {A : Type'} (s : A -> Prop) (_33177 : A) : (term53 A s _33177) = (s _33177).
Proof. exact (eq_refl (term53 A s _33177)). Qed.
Lemma lem3229231 {A : Type'} (_33178 : A) (s : A -> Prop) (x : A) (h1 : term101 A s x) : term53 A s _33178.
Proof. exact (@lem3229223 A s x h1 _33178). Qed.
Lemma lem3229232 {A : Type'} (s : A -> Prop) (_33178 : A) : (term53 A s _33178) = (s _33178).
Proof. exact (eq_refl (term53 A s _33178)). Qed.
Lemma lem3229235 {A : Type'} (x : A) (s : A -> Prop) (h1 : term89 A x s) : term35 A s x.
Proof. exact (proj1 (@lem3229200 A x s h1)). Qed.
Lemma lem3229241 {A : Type'} (s : A -> Prop) (x : A) (h1 : term101 A s x) : term35 A s x.
Proof. exact (proj2 (@lem3229201 A s x h1)). Qed.
Lemma lem3229243 {A : Type'} (_33177 : A) (x : A) (s : A -> Prop) (h1 : term89 A x s) : s _33177.
Proof. exact (EQ_MP (@lem3229229 A s _33177) (@lem3229228 A _33177 x s h1)). Qed.
Lemma lem3229244 {A : Type'} (_33177 : A) (x : A) (s : A -> Prop) (h1 : term89 A x s) : s _33177.
Proof. exact (@lem3229243 A _33177 x s h1). Qed.
Lemma lem3229245 {A : Type'} (x : A) (s : A -> Prop) (h1 : term89 A x s) : s x.
Proof. exact (@lem3229244 A x x s h1). Qed.
Lemma lem3229246 {A : Type'} (x : A) (s : A -> Prop) (h1 : term89 A x s) : term126 A s x.
Proof. exact (fun h0 : term35 A s x => @lem3229245 A x s h1). Qed.
Lemma lem3229248 (p : Prop) : (term127 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3229249 {A : Type'} (s : A -> Prop) (x : A) : (term126 A s x) = (s x).
Proof. exact (@lem3229248 (s x)). Qed.
Lemma lem3229250 {A : Type'} (x : A) (s : A -> Prop) (h1 : term89 A x s) : s x.
Proof. exact (EQ_MP (@lem3229249 A s x) (@lem3229246 A x s h1)). Qed.
Lemma lem3229253 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3229255 {A : Type'} (s : A -> Prop) (x : A) : (term35 A s x) = (term128 A s x).
Proof. exact (@lem3229253 (s x)). Qed.
Lemma lem3229258 {A : Type'} (x : A) (s : A -> Prop) (h1 : term89 A x s) : term128 A s x.
Proof. exact (EQ_MP (@lem3229255 A s x) (@lem3229235 A x s h1)). Qed.
Lemma lem3229261 {A : Type'} (x : A) (s : A -> Prop) (h1 : term89 A x s) : False.
Proof. exact (@lem3229258 A x s h1 (@lem3229250 A x s h1)). Qed.
Lemma lem3229262 {A : Type'} (x : A) (s : A -> Prop) (h1 : term89 A x s) : term129.
Proof. exact (fun h0 : ~ False => @lem3229261 A x s h1). Qed.
Lemma lem3229264 (p : Prop) : (term127 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3229265 : term129 = False.
Proof. exact (@lem3229264 False). Qed.
Lemma lem3229266 {A : Type'} (x : A) (s : A -> Prop) (h1 : term89 A x s) : False.
Proof. exact (EQ_MP (@lem3229265) (@lem3229262 A x s h1)). Qed.
Lemma lem3229268 {A : Type'} (_33178 : A) (s : A -> Prop) (x : A) (h1 : term101 A s x) : s _33178.
Proof. exact (EQ_MP (@lem3229232 A s _33178) (@lem3229231 A _33178 s x h1)). Qed.
Lemma lem3229269 {A : Type'} (_33178 : A) (s : A -> Prop) (x : A) (h1 : term101 A s x) : s _33178.
Proof. exact (@lem3229268 A _33178 s x h1). Qed.
Lemma lem3229270 {A : Type'} (s : A -> Prop) (x : A) (h1 : term101 A s x) : s x.
Proof. exact (@lem3229269 A x s x h1). Qed.
Lemma lem3229271 {A : Type'} (s : A -> Prop) (x : A) (h1 : term101 A s x) : term126 A s x.
Proof. exact (fun h0 : term35 A s x => @lem3229270 A s x h1). Qed.
Lemma lem3229273 (p : Prop) : (term127 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3229274 {A : Type'} (s : A -> Prop) (x : A) : (term126 A s x) = (s x).
Proof. exact (@lem3229273 (s x)). Qed.
Lemma lem3229275 {A : Type'} (s : A -> Prop) (x : A) (h1 : term101 A s x) : s x.
Proof. exact (EQ_MP (@lem3229274 A s x) (@lem3229271 A s x h1)). Qed.
Lemma lem3229278 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3229280 {A : Type'} (s : A -> Prop) (x : A) : (term35 A s x) = (term128 A s x).
Proof. exact (@lem3229278 (s x)). Qed.
Lemma lem3229283 {A : Type'} (s : A -> Prop) (x : A) (h1 : term101 A s x) : term128 A s x.
Proof. exact (EQ_MP (@lem3229280 A s x) (@lem3229241 A s x h1)). Qed.
Lemma lem3229286 {A : Type'} (s : A -> Prop) (x : A) (h1 : term101 A s x) : False.
Proof. exact (@lem3229283 A s x h1 (@lem3229275 A s x h1)). Qed.
Lemma lem3229287 {A : Type'} (s : A -> Prop) (x : A) (h1 : term101 A s x) : term129.
Proof. exact (fun h0 : ~ False => @lem3229286 A s x h1). Qed.
Lemma lem3229289 (p : Prop) : (term127 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3229290 : term129 = False.
Proof. exact (@lem3229289 False). Qed.
Lemma lem3229291 {A : Type'} (s : A -> Prop) (x : A) (h1 : term101 A s x) : False.
Proof. exact (EQ_MP (@lem3229290) (@lem3229287 A s x h1)). Qed.
Lemma lem3229292 {A : Type'} (s : A -> Prop) (x : A) (h1 : term122 A s x) : False.
Proof. exact (or_elim (@lem3229199 A s x h1) (fun h0 : term89 A x s => @lem3229266 A x s h0) (fun h0 : term101 A s x => @lem3229291 A s x h0)). Qed.
Lemma lem3229293 {A : Type'} (s : A -> Prop) (x : A) (h1 : term122 A s x) : (term122 A s x) = False.
Proof. exact (prop_ext (fun h2 : term122 A s x => @lem3229292 A s x h1) (fun h2 : False => @lem3229199 A s x h1)). Qed.
Lemma lem3229294 {A : Type'} (s : A -> Prop) (x : A) (h1 : term122 A s x) : False.
Proof. exact (EQ_MP (@lem3229293 A s x h1) (@lem3229199 A s x h1)). Qed.
Lemma lem3229295 {A : Type'} (s : A -> Prop) (h1 : term50 A s) : False.
Proof. exact (ex_elim (@lem3229166 A s h1) (fun x : A => fun h0 : term124 A s x => @lem3229294 A s x h0)). Qed.
Lemma lem3229296 {A : Type'} (s : A -> Prop) (h1 : term50 A s) : (term50 A s) = False.
Proof. exact (prop_ext (fun h2 : term50 A s => @lem3229295 A s h1) (fun h2 : False => @lem3229026 A s h1)). Qed.
Lemma lem3229297 {A : Type'} (s : A -> Prop) (h1 : term50 A s) : False.
Proof. exact (EQ_MP (@lem3229296 A s h1) (@lem3229026 A s h1)). Qed.
Lemma lem3229298 {A : Type'} (s : A -> Prop) : term49 A s.
Proof. exact (fun h0 : term50 A s => @lem3229297 A s h0). Qed.
Lemma lem3229299 {A : Type'} (s : A -> Prop) : (term31 A s) = (term38 A s).
Proof. exact (EQ_MP (@lem3229025 A s) (@lem3229298 A s)). Qed.
Lemma lem3229304 {A : Type'} : term40 A.
Proof. exact (fun s : A -> Prop => @lem3229299 A s). Qed.
Lemma lem3229305 {A : Type'} : term42 A.
Proof. exact (EQ_MP (@lem3229021 A) (@lem3229304 A)). Qed.
Lemma lem3229307 {A : Type'} : term42 A.
Proof. exact (@lem3228958 A (@lem3229305 A)). Qed.
Lemma lem3229308 {A : Type'} (h1 : term43 A) : False.
Proof. exact (@lem3229307 A (@lem3228942 A h1)). Qed.
Lemma lem3229309 {A : Type'} (h1 : term43 A) : (term43 A) = False.
Proof. exact (prop_ext (fun h2 : term43 A => @lem3229308 A h1) (fun h2 : False => @lem3228942 A h1)). Qed.
Lemma lem3229310 {A : Type'} (h1 : term43 A) : False.
Proof. exact (EQ_MP (@lem3229309 A h1) (@lem3228942 A h1)). Qed.
Lemma lem3229311 {A : Type'} : term42 A.
Proof. exact (fun h0 : term43 A => @lem3229310 A h0). Qed.
Lemma lem3229312 {A : Type'} : term40 A.
Proof. exact (EQ_MP (@lem3228941 A) (@lem3229311 A)). Qed.
Lemma lem3229313 {A : Type'} : term17 A.
Proof. exact (EQ_MP (@lem3228937 A) (@lem3229312 A)). Qed.
Lemma lem3229314 {A : Type'} : term16 A.
Proof. exact (EQ_MP (@lem3228831 A) (@lem3229313 A)). Qed.
