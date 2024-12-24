Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DELETE_COMM_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3307786 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3307787 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3307786 A s t). Qed.
Lemma lem3307788 {A : Type'} (s : A -> Prop) (y : A) (x : A) : ((term1 A s x y) = (term1 A s y x)) = (term2 A s y x).
Proof. exact (@lem3307787 A (term1 A s x y) (term1 A s y x)). Qed.
Lemma lem3307797 {A : Type'} (y : A) (x : A) : (term3 A y x) = (term4 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3307788 A s y x)). Qed.
Lemma lem3307798 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3307799 {A : Type'} (y : A) (x : A) : (term5 A y x) = (term6 A y x).
Proof. exact (MK_COMB (@lem3307798 A) (@lem3307797 A y x)). Qed.
Lemma lem3307804 {A : Type'} (x : A) : (term7 A x) = (term8 A x).
Proof. exact (fun_ext (fun y : A => @lem3307799 A y x)). Qed.
Lemma lem3307805 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3307806 {A : Type'} (x : A) : (term9 A x) = (term10 A x).
Proof. exact (MK_COMB (@lem3307805 A) (@lem3307804 A x)). Qed.
Lemma lem3307811 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (fun_ext (fun x : A => @lem3307806 A x)). Qed.
Lemma lem3307812 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3307813 {A : Type'} : (term13 A) = (term14 A).
Proof. exact (MK_COMB (@lem3307812 A) (@lem3307811 A)). Qed.
Lemma lem3307818 {A : Type'} : (term14 A) = (term13 A).
Proof. exact (SYM (@lem3307813 A)). Qed.
Lemma lem3307838 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term15 A x s y) = (term16 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3307839 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term15 A x s y) = (term16 A s x y).
Proof. exact (@lem3307838 A s x y). Qed.
Lemma lem3307840 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) : (term17 A x' s x y) = (term18 A s x x' y).
Proof. exact (@lem3307839 A (@DELETE A s x) x' y). Qed.
Lemma lem3307844 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term15 A x s y) = (term16 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3307845 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term15 A x s y) = (term16 A s x y).
Proof. exact (@lem3307844 A s x y). Qed.
Lemma lem3307846 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term15 A x' s x) = (term16 A s x' x).
Proof. exact (@lem3307845 A s x' x). Qed.
Lemma lem3307850 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3307851 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3307850 A P x). Qed.
Lemma lem3307852 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3307851 A s x'). Qed.
Lemma lem3307853 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3307854 {A : Type'} (s : A -> Prop) (x' : A) : (term19 A x' s) = (term20 A s x').
Proof. exact (MK_COMB (@lem3307853) (@lem3307852 A s x')). Qed.
Lemma lem3307857 {A : Type'} (x' : A) (x : A) : (term21 A x' x) = (term21 A x' x).
Proof. exact (eq_refl (term21 A x' x)). Qed.
Lemma lem3307858 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term16 A s x' x) = (term22 A s x' x).
Proof. exact (MK_COMB (@lem3307854 A s x') (@lem3307857 A x' x)). Qed.
Lemma lem3307861 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term15 A x' s x) = (term22 A s x' x).
Proof. exact (TRANS (@lem3307846 A s x' x) (@lem3307858 A s x' x)). Qed.
Lemma lem3307862 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3307863 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term23 A x' s x) = (term24 A s x' x).
Proof. exact (MK_COMB (@lem3307862) (@lem3307861 A s x' x)). Qed.
Lemma lem3307866 {A : Type'} (x' : A) (y : A) : (term21 A x' y) = (term21 A x' y).
Proof. exact (eq_refl (term21 A x' y)). Qed.
Lemma lem3307867 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) : (term18 A s x x' y) = (term25 A s x x' y).
Proof. exact (MK_COMB (@lem3307863 A s x' x) (@lem3307866 A x' y)). Qed.
Lemma lem3307870 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) : (term17 A x' s x y) = (term25 A s x x' y).
Proof. exact (TRANS (@lem3307840 A s x x' y) (@lem3307867 A s x x' y)). Qed.
Lemma lem3307871 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3307872 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) : (term26 A x' s x y) = (term27 A s x x' y).
Proof. exact (MK_COMB (@lem3307871) (@lem3307870 A s x x' y)). Qed.
Lemma lem3307874 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term15 A x s y) = (term16 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3307875 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term15 A x s y) = (term16 A s x y).
Proof. exact (@lem3307874 A s x y). Qed.
Lemma lem3307876 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term17 A x' s y x) = (term18 A s y x' x).
Proof. exact (@lem3307875 A (@DELETE A s y) x' x). Qed.
Lemma lem3307880 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term15 A x s y) = (term16 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3307881 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term15 A x s y) = (term16 A s x y).
Proof. exact (@lem3307880 A s x y). Qed.
Lemma lem3307882 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term15 A x' s y) = (term16 A s x' y).
Proof. exact (@lem3307881 A s x' y). Qed.
Lemma lem3307886 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3307887 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3307886 A P x). Qed.
Lemma lem3307888 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3307887 A s x'). Qed.
Lemma lem3307889 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3307890 {A : Type'} (s : A -> Prop) (x' : A) : (term19 A x' s) = (term20 A s x').
Proof. exact (MK_COMB (@lem3307889) (@lem3307888 A s x')). Qed.
Lemma lem3307893 {A : Type'} (x' : A) (y : A) : (term21 A x' y) = (term21 A x' y).
Proof. exact (eq_refl (term21 A x' y)). Qed.
Lemma lem3307894 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term16 A s x' y) = (term22 A s x' y).
Proof. exact (MK_COMB (@lem3307890 A s x') (@lem3307893 A x' y)). Qed.
Lemma lem3307897 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term15 A x' s y) = (term22 A s x' y).
Proof. exact (TRANS (@lem3307882 A s x' y) (@lem3307894 A s x' y)). Qed.
Lemma lem3307898 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3307899 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term23 A x' s y) = (term24 A s x' y).
Proof. exact (MK_COMB (@lem3307898) (@lem3307897 A s x' y)). Qed.
Lemma lem3307902 {A : Type'} (x' : A) (x : A) : (term21 A x' x) = (term21 A x' x).
Proof. exact (eq_refl (term21 A x' x)). Qed.
Lemma lem3307903 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term18 A s y x' x) = (term25 A s y x' x).
Proof. exact (MK_COMB (@lem3307899 A s x' y) (@lem3307902 A x' x)). Qed.
Lemma lem3307906 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term17 A x' s y x) = (term25 A s y x' x).
Proof. exact (TRANS (@lem3307876 A s y x' x) (@lem3307903 A s y x' x)). Qed.
Lemma lem3307907 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : ((term17 A x' s x y) = (term17 A x' s y x)) = ((term25 A s x x' y) = (term25 A s y x' x)).
Proof. exact (MK_COMB (@lem3307872 A s x x' y) (@lem3307906 A s y x' x)). Qed.
Lemma lem3307910 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term28 A s y x) = (term29 A s y x).
Proof. exact (fun_ext (fun x' : A => @lem3307907 A s y x' x)). Qed.
Lemma lem3307911 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3307912 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term2 A s y x) = (term30 A s y x).
Proof. exact (MK_COMB (@lem3307911 A) (@lem3307910 A s y x)). Qed.
Lemma lem3307917 {A : Type'} (y : A) (x : A) : (term4 A y x) = (term31 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3307912 A s y x)). Qed.
Lemma lem3307918 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3307919 {A : Type'} (y : A) (x : A) : (term6 A y x) = (term32 A y x).
Proof. exact (MK_COMB (@lem3307918 A) (@lem3307917 A y x)). Qed.
Lemma lem3307924 {A : Type'} (x : A) : (term8 A x) = (term33 A x).
Proof. exact (fun_ext (fun y : A => @lem3307919 A y x)). Qed.
Lemma lem3307925 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3307926 {A : Type'} (x : A) : (term10 A x) = (term34 A x).
Proof. exact (MK_COMB (@lem3307925 A) (@lem3307924 A x)). Qed.
Lemma lem3307931 {A : Type'} : (term12 A) = (term35 A).
Proof. exact (fun_ext (fun x : A => @lem3307926 A x)). Qed.
Lemma lem3307932 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3307933 {A : Type'} : (term14 A) = (term36 A).
Proof. exact (MK_COMB (@lem3307932 A) (@lem3307931 A)). Qed.
Lemma lem3307938 {A : Type'} : (term36 A) = (term14 A).
Proof. exact (SYM (@lem3307933 A)). Qed.
Lemma lem3307940 (p : Prop) : p = (term37 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3307941 {A : Type'} : (term36 A) = (term38 A).
Proof. exact (@lem3307940 (term36 A)). Qed.
Lemma lem3307942 {A : Type'} : (term38 A) = (term36 A).
Proof. exact (SYM (@lem3307941 A)). Qed.
Lemma lem3307943 {A : Type'} (h1 : term39 A) : term39 A.
Proof. exact (h1). Qed.
Lemma lem3307946 {A : Type'} (h1 : term38 A) : term38 A.
Proof. exact (h1). Qed.
Lemma lem3307947 {A : Type'} : term40 A.
Proof. exact (fun h0 : term38 A => @lem3307946 A h0). Qed.
Lemma lem3307948 {A : Type'} (h1 : term40 A) : term40 A.
Proof. exact (h1). Qed.
Lemma lem3307949 {A : Type'} (h1 : term38 A) : term38 A.
Proof. exact (h1). Qed.
Lemma lem3307950 {A : Type'} (h1 : term38 A) (h2 : term40 A) : term38 A.
Proof. exact (@lem3307948 A h2 (@lem3307949 A h1)). Qed.
Lemma lem3307951 {A : Type'} (h1 : term38 A) : term41 A.
Proof. exact (fun h0 : term40 A => @lem3307950 A h1 h0). Qed.
Lemma lem3307952 {A : Type'} (h1 : term40 A) : term40 A.
Proof. exact (h1). Qed.
Lemma lem3307953 {A : Type'} (h1 : term38 A) (h2 : term40 A) : term38 A.
Proof. exact (@lem3307951 A h1 (@lem3307952 A h2)). Qed.
Lemma lem3307954 {A : Type'} (h1 : term40 A) : term40 A.
Proof. exact (fun h0 : term38 A => @lem3307953 A h0 h1). Qed.
Lemma lem3307955 {A : Type'} : term42 A.
Proof. exact (fun h0 : term40 A => @lem3307954 A h0). Qed.
Lemma lem3307958 {A : Type'} : term40 A.
Proof. exact (@lem3307955 A (@lem3307947 A)). Qed.
Lemma lem3307959 {A : Type'} : term40 A.
Proof. exact (@lem3307958 A). Qed.
Lemma lem3307961 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3307962 {A : Type'} : (term38 A) = (term43 A).
Proof. exact (@lem3307961 (term39 A)). Qed.
Lemma lem3307964 (t : Prop) : (term44 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3307965 {A : Type'} : (term43 A) = (term36 A).
Proof. exact (@lem3307964 (term36 A)). Qed.
Lemma lem3307994 {A : Type'} : (term38 A) = (term36 A).
Proof. exact (TRANS (@lem3307962 A) (@lem3307965 A)). Qed.
Lemma lem3308023 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : ((term25 A s x x' y) = (term25 A s y x' x)) = ((term25 A s x x' y) = (term25 A s y x' x)).
Proof. exact (eq_refl ((term25 A s x x' y) = (term25 A s y x' x))). Qed.
Lemma lem3308024 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term29 A s y x) = (term29 A s y x).
Proof. exact (fun_ext (fun x' : A => @lem3308023 A s y x' x)). Qed.
Lemma lem3308025 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3308026 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term30 A s y x) = (term30 A s y x).
Proof. exact (MK_COMB (@lem3308025 A) (@lem3308024 A s y x)). Qed.
Lemma lem3308027 {A : Type'} (y : A) (x : A) : (term31 A y x) = (term31 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3308026 A s y x)). Qed.
Lemma lem3308028 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3308029 {A : Type'} (y : A) (x : A) : (term32 A y x) = (term32 A y x).
Proof. exact (MK_COMB (@lem3308028 A) (@lem3308027 A y x)). Qed.
Lemma lem3308030 {A : Type'} (x : A) : (term33 A x) = (term33 A x).
Proof. exact (fun_ext (fun y : A => @lem3308029 A y x)). Qed.
Lemma lem3308031 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3308032 {A : Type'} (x : A) : (term34 A x) = (term34 A x).
Proof. exact (MK_COMB (@lem3308031 A) (@lem3308030 A x)). Qed.
Lemma lem3308033 {A : Type'} : (term35 A) = (term35 A).
Proof. exact (fun_ext (fun x : A => @lem3308032 A x)). Qed.
Lemma lem3308034 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3308035 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (MK_COMB (@lem3308034 A) (@lem3308033 A)). Qed.
Lemma lem3308070 {A : Type'} : (term38 A) = (term36 A).
Proof. exact (TRANS (@lem3307994 A) (@lem3308035 A)). Qed.
Lemma lem3308071 {A : Type'} : (term36 A) = (term38 A).
Proof. exact (SYM (@lem3308070 A)). Qed.
Lemma lem3308073 (p : Prop) : p = (term37 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3308074 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : ((term25 A s x x' y) = (term25 A s y x' x)) = (term45 A s y x' x).
Proof. exact (@lem3308073 ((term25 A s x x' y) = (term25 A s y x' x))). Qed.
Lemma lem3308075 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term45 A s y x' x) = ((term25 A s x x' y) = (term25 A s y x' x)).
Proof. exact (SYM (@lem3308074 A s y x' x)). Qed.
Lemma lem3308076 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term46 A s y x' x) : term46 A s y x' x.
Proof. exact (h1). Qed.
Lemma lem3308082 {A : Type'} (x' : A) (x : A) : (term47 A x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3308084 {A : Type'} (s : A -> Prop) (x' : A) : (term48 A s x') = (term48 A s x').
Proof. exact (eq_refl (term48 A s x')). Qed.
Lemma lem3308085 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term49 A s x' x) = (term50 A s x' x).
Proof. exact (MK_COMB (@lem3308084 A s x') (@lem3308082 A x' x)). Qed.
Lemma lem3308086 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term51 A s x' x) = (term49 A s x' x).
Proof. exact (@lem17045 (s x') (term21 A x' x)). Qed.
Lemma lem3308087 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term51 A s x' x) = (term50 A s x' x).
Proof. exact (TRANS (@lem3308086 A s x' x) (@lem3308085 A s x' x)). Qed.
Lemma lem3308094 {A : Type'} (x' : A) (y : A) : (term47 A x' y) = (x' = y).
Proof. exact (@lem16933 (x' = y)). Qed.
Lemma lem3308095 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3308096 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term52 A s x' x) = (term53 A s x' x).
Proof. exact (MK_COMB (@lem3308095) (@lem3308087 A s x' x)). Qed.
Lemma lem3308097 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) : (term54 A s x x' y) = (term55 A s x x' y).
Proof. exact (MK_COMB (@lem3308096 A s x' x) (@lem3308094 A x' y)). Qed.
Lemma lem3308098 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) : (term56 A s x x' y) = (term54 A s x x' y).
Proof. exact (@lem17045 (term22 A s x' x) (term21 A x' y)). Qed.
Lemma lem3308099 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) : (term56 A s x x' y) = (term55 A s x x' y).
Proof. exact (TRANS (@lem3308098 A s x x' y) (@lem3308097 A s x x' y)). Qed.
Lemma lem3308108 {A : Type'} (x' : A) (y : A) : (term47 A x' y) = (x' = y).
Proof. exact (@lem16933 (x' = y)). Qed.
Lemma lem3308110 {A : Type'} (s : A -> Prop) (x' : A) : (term48 A s x') = (term48 A s x').
Proof. exact (eq_refl (term48 A s x')). Qed.
Lemma lem3308111 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term49 A s x' y) = (term50 A s x' y).
Proof. exact (MK_COMB (@lem3308110 A s x') (@lem3308108 A x' y)). Qed.
Lemma lem3308112 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term51 A s x' y) = (term49 A s x' y).
Proof. exact (@lem17045 (s x') (term21 A x' y)). Qed.
Lemma lem3308113 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term51 A s x' y) = (term50 A s x' y).
Proof. exact (TRANS (@lem3308112 A s x' y) (@lem3308111 A s x' y)). Qed.
Lemma lem3308120 {A : Type'} (x' : A) (x : A) : (term47 A x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3308121 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3308122 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term52 A s x' y) = (term53 A s x' y).
Proof. exact (MK_COMB (@lem3308121) (@lem3308113 A s x' y)). Qed.
Lemma lem3308123 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term54 A s y x' x) = (term55 A s y x' x).
Proof. exact (MK_COMB (@lem3308122 A s x' y) (@lem3308120 A x' x)). Qed.
Lemma lem3308124 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term56 A s y x' x) = (term54 A s y x' x).
Proof. exact (@lem17045 (term22 A s x' y) (term21 A x' x)). Qed.
Lemma lem3308125 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term56 A s y x' x) = (term55 A s y x' x).
Proof. exact (TRANS (@lem3308124 A s y x' x) (@lem3308123 A s y x' x)). Qed.
Lemma lem3308128 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term25 A s y x' x) = (term25 A s y x' x).
Proof. exact (eq_refl (term25 A s y x' x)). Qed.
Lemma lem3308129 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3308130 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) : (term57 A s x x' y) = (term58 A s x x' y).
Proof. exact (MK_COMB (@lem3308129) (@lem3308099 A s x x' y)). Qed.
Lemma lem3308131 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term59 A s y x' x) = (term60 A s y x' x).
Proof. exact (MK_COMB (@lem3308130 A s x x' y) (@lem3308128 A s y x' x)). Qed.
Lemma lem3308133 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) : (term61 A s x x' y) = (term61 A s x x' y).
Proof. exact (eq_refl (term61 A s x x' y)). Qed.
Lemma lem3308134 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term62 A s y x' x) = (term63 A s y x' x).
Proof. exact (MK_COMB (@lem3308133 A s x x' y) (@lem3308125 A s y x' x)). Qed.
Lemma lem3308135 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3308136 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term64 A s y x' x) = (term65 A s y x' x).
Proof. exact (MK_COMB (@lem3308135) (@lem3308134 A s y x' x)). Qed.
Lemma lem3308137 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term66 A s y x' x) = (term67 A s y x' x).
Proof. exact (MK_COMB (@lem3308136 A s y x' x) (@lem3308131 A s y x' x)). Qed.
Lemma lem3308138 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term46 A s y x' x) = (term66 A s y x' x).
Proof. exact (@lem17646 (term25 A s x x' y) (term25 A s y x' x)). Qed.
Lemma lem3308143 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term46 A s y x' x) = (term67 A s y x' x).
Proof. exact (TRANS (@lem3308138 A s y x' x) (@lem3308137 A s y x' x)). Qed.
Lemma lem3308242 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term46 A s y x' x) : term67 A s y x' x.
Proof. exact (EQ_MP (@lem3308143 A s y x' x) (@lem3308076 A s y x' x h1)). Qed.
Lemma lem3308243 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term63 A s y x' x) : term63 A s y x' x.
Proof. exact (h1). Qed.
Lemma lem3308244 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term60 A s y x' x) : term60 A s y x' x.
Proof. exact (h1). Qed.
Lemma lem3308245 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term63 A s y x' x) : term55 A s y x' x.
Proof. exact (proj2 (@lem3308243 A s y x' x h1)). Qed.
Lemma lem3308246 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term63 A s y x' x) : term25 A s x x' y.
Proof. exact (proj1 (@lem3308243 A s y x' x h1)). Qed.
Lemma lem3308248 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term63 A s y x' x) : term22 A s x' x.
Proof. exact (proj1 (@lem3308246 A s y x' x h1)). Qed.
Lemma lem3308251 {A : Type'} (s : A -> Prop) (x' : A) (y : A) (h1 : term50 A s x' y) : term50 A s x' y.
Proof. exact (h1). Qed.
Lemma lem3308255 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term60 A s y x' x) : term25 A s y x' x.
Proof. exact (proj2 (@lem3308244 A s y x' x h1)). Qed.
Lemma lem3308256 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term60 A s y x' x) : term55 A s x x' y.
Proof. exact (proj1 (@lem3308244 A s y x' x h1)). Qed.
Lemma lem3308258 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term60 A s y x' x) : term22 A s x' y.
Proof. exact (proj1 (@lem3308255 A s y x' x h1)). Qed.
Lemma lem3308261 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term50 A s x' x) : term50 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3308280 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term68 A s x') : term68 A s x'.
Proof. exact (h1). Qed.
Lemma lem3308296 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem3308312 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3308328 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term68 A s x') : term68 A s x'.
Proof. exact (h1). Qed.
Lemma lem3308344 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3308360 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem3308368 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term68 A s x') : term68 A s x'.
Proof. exact (h1). Qed.
Lemma lem3308370 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term63 A s y x' x) : term21 A x' y.
Proof. exact (proj2 (@lem3308246 A s y x' x h1)). Qed.
Lemma lem3308376 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem3308382 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term63 A s y x' x) : term21 A x' x.
Proof. exact (proj2 (@lem3308248 A s y x' x h1)). Qed.
Lemma lem3308384 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3308392 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term68 A s x') : term68 A s x'.
Proof. exact (h1). Qed.
Lemma lem3308394 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term60 A s y x' x) : term21 A x' x.
Proof. exact (proj2 (@lem3308255 A s y x' x h1)). Qed.
Lemma lem3308400 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3308406 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term60 A s y x' x) : term21 A x' y.
Proof. exact (proj2 (@lem3308258 A s y x' x h1)). Qed.
Lemma lem3308408 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem3308423 {A : Type'} (y : A) : (term69 A y) = (term69 A y).
Proof. exact (eq_refl (term69 A y)). Qed.
Lemma lem3308424 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : (term70 A y x') = (term71 A y).
Proof. exact (MK_COMB (@lem3308423 A y) (@lem3308376 A x' y h1)). Qed.
Lemma lem3308425 {A : Type'} (y : A) : (term71 A y) = (term72 A y).
Proof. exact (eq_refl (term71 A y)). Qed.
Lemma lem3308426 {A : Type'} (y : A) (x' : A) : (term73 A y x') = (term73 A y x').
Proof. exact (eq_refl (term73 A y x')). Qed.
Lemma lem3308427 {A : Type'} (x' : A) (y : A) : ((term70 A y x') = (term71 A y)) = ((term70 A y x') = (term72 A y)).
Proof. exact (MK_COMB (@lem3308426 A y x') (@lem3308425 A y)). Qed.
Lemma lem3308428 {A : Type'} (x' : A) (y : A) : (term70 A y x') = (term21 A x' y).
Proof. exact (eq_refl (term70 A y x')). Qed.
Lemma lem3308429 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3308430 {A : Type'} (x' : A) (y : A) : (term73 A y x') = (term74 A x' y).
Proof. exact (MK_COMB (@lem3308429) (@lem3308428 A x' y)). Qed.
Lemma lem3308431 {A : Type'} (y : A) : (term72 A y) = (term72 A y).
Proof. exact (eq_refl (term72 A y)). Qed.
Lemma lem3308432 {A : Type'} (x' : A) (y : A) : ((term70 A y x') = (term72 A y)) = ((term21 A x' y) = (term72 A y)).
Proof. exact (MK_COMB (@lem3308430 A x' y) (@lem3308431 A y)). Qed.
Lemma lem3308433 {A : Type'} (x' : A) (y : A) : ((term70 A y x') = (term71 A y)) = ((term21 A x' y) = (term72 A y)).
Proof. exact (TRANS (@lem3308427 A x' y) (@lem3308432 A x' y)). Qed.
Lemma lem3308434 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : (term21 A x' y) = (term72 A y).
Proof. exact (EQ_MP (@lem3308433 A x' y) (@lem3308424 A x' y h1)). Qed.
Lemma lem3308435 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term63 A s y x' x) (h2 : x' = y) : term72 A y.
Proof. exact (EQ_MP (@lem3308434 A x' y h2) (@lem3308370 A s y x' x h1)). Qed.
Lemma lem3308502 {A : Type'} (x : A) : (term69 A x) = (term69 A x).
Proof. exact (eq_refl (term69 A x)). Qed.
Lemma lem3308503 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term70 A x x') = (term71 A x).
Proof. exact (MK_COMB (@lem3308502 A x) (@lem3308384 A x' x h1)). Qed.
Lemma lem3308504 {A : Type'} (x : A) : (term71 A x) = (term72 A x).
Proof. exact (eq_refl (term71 A x)). Qed.
Lemma lem3308505 {A : Type'} (x : A) (x' : A) : (term73 A x x') = (term73 A x x').
Proof. exact (eq_refl (term73 A x x')). Qed.
Lemma lem3308506 {A : Type'} (x' : A) (x : A) : ((term70 A x x') = (term71 A x)) = ((term70 A x x') = (term72 A x)).
Proof. exact (MK_COMB (@lem3308505 A x x') (@lem3308504 A x)). Qed.
Lemma lem3308507 {A : Type'} (x' : A) (x : A) : (term70 A x x') = (term21 A x' x).
Proof. exact (eq_refl (term70 A x x')). Qed.
Lemma lem3308508 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3308509 {A : Type'} (x' : A) (x : A) : (term73 A x x') = (term74 A x' x).
Proof. exact (MK_COMB (@lem3308508) (@lem3308507 A x' x)). Qed.
Lemma lem3308510 {A : Type'} (x : A) : (term72 A x) = (term72 A x).
Proof. exact (eq_refl (term72 A x)). Qed.
Lemma lem3308511 {A : Type'} (x' : A) (x : A) : ((term70 A x x') = (term72 A x)) = ((term21 A x' x) = (term72 A x)).
Proof. exact (MK_COMB (@lem3308509 A x' x) (@lem3308510 A x)). Qed.
Lemma lem3308512 {A : Type'} (x' : A) (x : A) : ((term70 A x x') = (term71 A x)) = ((term21 A x' x) = (term72 A x)).
Proof. exact (TRANS (@lem3308506 A x' x) (@lem3308511 A x' x)). Qed.
Lemma lem3308513 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term21 A x' x) = (term72 A x).
Proof. exact (EQ_MP (@lem3308512 A x' x) (@lem3308503 A x' x h1)). Qed.
Lemma lem3308514 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term63 A s y x' x) (h2 : x' = x) : term72 A x.
Proof. exact (EQ_MP (@lem3308513 A x' x h2) (@lem3308382 A s y x' x h1)). Qed.
Lemma lem3308529 {A : Type'} (x : A) : (term69 A x) = (term69 A x).
Proof. exact (eq_refl (term69 A x)). Qed.
Lemma lem3308530 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term70 A x x') = (term71 A x).
Proof. exact (MK_COMB (@lem3308529 A x) (@lem3308400 A x' x h1)). Qed.
Lemma lem3308531 {A : Type'} (x : A) : (term71 A x) = (term72 A x).
Proof. exact (eq_refl (term71 A x)). Qed.
Lemma lem3308532 {A : Type'} (x : A) (x' : A) : (term73 A x x') = (term73 A x x').
Proof. exact (eq_refl (term73 A x x')). Qed.
Lemma lem3308533 {A : Type'} (x' : A) (x : A) : ((term70 A x x') = (term71 A x)) = ((term70 A x x') = (term72 A x)).
Proof. exact (MK_COMB (@lem3308532 A x x') (@lem3308531 A x)). Qed.
Lemma lem3308534 {A : Type'} (x' : A) (x : A) : (term70 A x x') = (term21 A x' x).
Proof. exact (eq_refl (term70 A x x')). Qed.
Lemma lem3308535 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3308536 {A : Type'} (x' : A) (x : A) : (term73 A x x') = (term74 A x' x).
Proof. exact (MK_COMB (@lem3308535) (@lem3308534 A x' x)). Qed.
Lemma lem3308537 {A : Type'} (x : A) : (term72 A x) = (term72 A x).
Proof. exact (eq_refl (term72 A x)). Qed.
Lemma lem3308538 {A : Type'} (x' : A) (x : A) : ((term70 A x x') = (term72 A x)) = ((term21 A x' x) = (term72 A x)).
Proof. exact (MK_COMB (@lem3308536 A x' x) (@lem3308537 A x)). Qed.
Lemma lem3308539 {A : Type'} (x' : A) (x : A) : ((term70 A x x') = (term71 A x)) = ((term21 A x' x) = (term72 A x)).
Proof. exact (TRANS (@lem3308533 A x' x) (@lem3308538 A x' x)). Qed.
Lemma lem3308540 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term21 A x' x) = (term72 A x).
Proof. exact (EQ_MP (@lem3308539 A x' x) (@lem3308530 A x' x h1)). Qed.
Lemma lem3308541 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term60 A s y x' x) (h2 : x' = x) : term72 A x.
Proof. exact (EQ_MP (@lem3308540 A x' x h2) (@lem3308394 A s y x' x h1)). Qed.
Lemma lem3308608 {A : Type'} (y : A) : (term69 A y) = (term69 A y).
Proof. exact (eq_refl (term69 A y)). Qed.
Lemma lem3308609 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : (term70 A y x') = (term71 A y).
Proof. exact (MK_COMB (@lem3308608 A y) (@lem3308408 A x' y h1)). Qed.
Lemma lem3308610 {A : Type'} (y : A) : (term71 A y) = (term72 A y).
Proof. exact (eq_refl (term71 A y)). Qed.
Lemma lem3308611 {A : Type'} (y : A) (x' : A) : (term73 A y x') = (term73 A y x').
Proof. exact (eq_refl (term73 A y x')). Qed.
Lemma lem3308612 {A : Type'} (x' : A) (y : A) : ((term70 A y x') = (term71 A y)) = ((term70 A y x') = (term72 A y)).
Proof. exact (MK_COMB (@lem3308611 A y x') (@lem3308610 A y)). Qed.
Lemma lem3308613 {A : Type'} (x' : A) (y : A) : (term70 A y x') = (term21 A x' y).
Proof. exact (eq_refl (term70 A y x')). Qed.
Lemma lem3308614 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3308615 {A : Type'} (x' : A) (y : A) : (term73 A y x') = (term74 A x' y).
Proof. exact (MK_COMB (@lem3308614) (@lem3308613 A x' y)). Qed.
Lemma lem3308616 {A : Type'} (y : A) : (term72 A y) = (term72 A y).
Proof. exact (eq_refl (term72 A y)). Qed.
Lemma lem3308617 {A : Type'} (x' : A) (y : A) : ((term70 A y x') = (term72 A y)) = ((term21 A x' y) = (term72 A y)).
Proof. exact (MK_COMB (@lem3308615 A x' y) (@lem3308616 A y)). Qed.
Lemma lem3308618 {A : Type'} (x' : A) (y : A) : ((term70 A y x') = (term71 A y)) = ((term21 A x' y) = (term72 A y)).
Proof. exact (TRANS (@lem3308612 A x' y) (@lem3308617 A x' y)). Qed.
Lemma lem3308619 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : (term21 A x' y) = (term72 A y).
Proof. exact (EQ_MP (@lem3308618 A x' y) (@lem3308609 A x' y h1)). Qed.
Lemma lem3308620 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term60 A s y x' x) (h2 : x' = y) : term72 A y.
Proof. exact (EQ_MP (@lem3308619 A x' y h2) (@lem3308406 A s y x' x h1)). Qed.
Lemma lem3308636 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term63 A s y x' x) : s x'.
Proof. exact (proj1 (@lem3308248 A s y x' x h1)). Qed.
Lemma lem3308637 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term63 A s y x' x) : term75 A s x'.
Proof. exact (fun h0 : term68 A s x' => @lem3308636 A s y x' x h1). Qed.
Lemma lem3308639 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3308640 {A : Type'} (s : A -> Prop) (x' : A) : (term75 A s x') = (s x').
Proof. exact (@lem3308639 (s x')). Qed.
Lemma lem3308641 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term63 A s y x' x) : s x'.
Proof. exact (EQ_MP (@lem3308640 A s x') (@lem3308637 A s y x' x h1)). Qed.
Lemma lem3308644 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3308646 {A : Type'} (s : A -> Prop) (x' : A) : (term68 A s x') = (term77 A s x').
Proof. exact (@lem3308644 (s x')). Qed.
Lemma lem3308649 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term68 A s x') : term77 A s x'.
Proof. exact (EQ_MP (@lem3308646 A s x') (@lem3308368 A s x' h1)). Qed.
Lemma lem3308652 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term68 A s x') (h2 : term63 A s y x' x) : False.
Proof. exact (@lem3308649 A s x' h1 (@lem3308641 A s y x' x h2)). Qed.
Lemma lem3308653 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term68 A s x') (h2 : term63 A s y x' x) : term78.
Proof. exact (fun h0 : ~ False => @lem3308652 A s y x' x h1 h2). Qed.
Lemma lem3308655 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3308656 : term78 = False.
Proof. exact (@lem3308655 False). Qed.
Lemma lem3308657 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term68 A s x') (h2 : term63 A s y x' x) : False.
Proof. exact (EQ_MP (@lem3308656) (@lem3308653 A s y x' x h1 h2)). Qed.
Lemma lem3308673 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3308674 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3308673 A x). Qed.
Lemma lem3308675 {A : Type'} (y : A) : y = y.
Proof. exact (@lem3308674 A y). Qed.
Lemma lem3308676 {A : Type'} (y : A) : term79 A y.
Proof. exact (fun h0 : term72 A y => @lem3308675 A y). Qed.
Lemma lem3308678 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3308679 {A : Type'} (y : A) : (term79 A y) = (y = y).
Proof. exact (@lem3308678 (y = y)). Qed.
Lemma lem3308680 {A : Type'} (y : A) : y = y.
Proof. exact (EQ_MP (@lem3308679 A y) (@lem3308676 A y)). Qed.
Lemma lem3308683 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3308685 {A : Type'} (y : A) : (term72 A y) = (term80 A y).
Proof. exact (@lem3308683 (y = y)). Qed.
Lemma lem3308688 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term63 A s y x' x) (h2 : x' = y) : term80 A y.
Proof. exact (EQ_MP (@lem3308685 A y) (@lem3308435 A s x x' y h1 h2)). Qed.
Lemma lem3308691 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term63 A s y x' x) (h2 : x' = y) : False.
Proof. exact (@lem3308688 A s x x' y h1 h2 (@lem3308680 A y)). Qed.
Lemma lem3308692 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term63 A s y x' x) (h2 : x' = y) : term78.
Proof. exact (fun h0 : ~ False => @lem3308691 A s x x' y h1 h2). Qed.
Lemma lem3308694 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3308695 : term78 = False.
Proof. exact (@lem3308694 False). Qed.
Lemma lem3308712 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3308713 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3308712 A x). Qed.
Lemma lem3308714 {A : Type'} (x : A) : term79 A x.
Proof. exact (fun h0 : term72 A x => @lem3308713 A x). Qed.
Lemma lem3308716 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3308717 {A : Type'} (x : A) : (term79 A x) = (x = x).
Proof. exact (@lem3308716 (x = x)). Qed.
Lemma lem3308718 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3308717 A x) (@lem3308714 A x)). Qed.
Lemma lem3308721 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3308723 {A : Type'} (x : A) : (term72 A x) = (term80 A x).
Proof. exact (@lem3308721 (x = x)). Qed.
Lemma lem3308726 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term63 A s y x' x) (h2 : x' = x) : term80 A x.
Proof. exact (EQ_MP (@lem3308723 A x) (@lem3308514 A s y x' x h1 h2)). Qed.
Lemma lem3308729 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term63 A s y x' x) (h2 : x' = x) : False.
Proof. exact (@lem3308726 A s y x' x h1 h2 (@lem3308718 A x)). Qed.
Lemma lem3308730 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term63 A s y x' x) (h2 : x' = x) : term78.
Proof. exact (fun h0 : ~ False => @lem3308729 A s y x' x h1 h2). Qed.
Lemma lem3308732 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3308733 : term78 = False.
Proof. exact (@lem3308732 False). Qed.
Lemma lem3308750 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term60 A s y x' x) : s x'.
Proof. exact (proj1 (@lem3308258 A s y x' x h1)). Qed.
Lemma lem3308751 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term60 A s y x' x) : term75 A s x'.
Proof. exact (fun h0 : term68 A s x' => @lem3308750 A s y x' x h1). Qed.
Lemma lem3308753 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3308754 {A : Type'} (s : A -> Prop) (x' : A) : (term75 A s x') = (s x').
Proof. exact (@lem3308753 (s x')). Qed.
Lemma lem3308755 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term60 A s y x' x) : s x'.
Proof. exact (EQ_MP (@lem3308754 A s x') (@lem3308751 A s y x' x h1)). Qed.
Lemma lem3308758 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3308760 {A : Type'} (s : A -> Prop) (x' : A) : (term68 A s x') = (term77 A s x').
Proof. exact (@lem3308758 (s x')). Qed.
Lemma lem3308763 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term68 A s x') : term77 A s x'.
Proof. exact (EQ_MP (@lem3308760 A s x') (@lem3308392 A s x' h1)). Qed.
Lemma lem3308766 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term68 A s x') (h2 : term60 A s y x' x) : False.
Proof. exact (@lem3308763 A s x' h1 (@lem3308755 A s y x' x h2)). Qed.
Lemma lem3308767 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term68 A s x') (h2 : term60 A s y x' x) : term78.
Proof. exact (fun h0 : ~ False => @lem3308766 A s y x' x h1 h2). Qed.
Lemma lem3308769 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3308770 : term78 = False.
Proof. exact (@lem3308769 False). Qed.
Lemma lem3308771 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term68 A s x') (h2 : term60 A s y x' x) : False.
Proof. exact (EQ_MP (@lem3308770) (@lem3308767 A s y x' x h1 h2)). Qed.
Lemma lem3308787 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3308788 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3308787 A x). Qed.
Lemma lem3308789 {A : Type'} (x : A) : term79 A x.
Proof. exact (fun h0 : term72 A x => @lem3308788 A x). Qed.
Lemma lem3308791 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3308792 {A : Type'} (x : A) : (term79 A x) = (x = x).
Proof. exact (@lem3308791 (x = x)). Qed.
Lemma lem3308793 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3308792 A x) (@lem3308789 A x)). Qed.
Lemma lem3308796 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3308798 {A : Type'} (x : A) : (term72 A x) = (term80 A x).
Proof. exact (@lem3308796 (x = x)). Qed.
Lemma lem3308801 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term60 A s y x' x) (h2 : x' = x) : term80 A x.
Proof. exact (EQ_MP (@lem3308798 A x) (@lem3308541 A s y x' x h1 h2)). Qed.
Lemma lem3308804 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term60 A s y x' x) (h2 : x' = x) : False.
Proof. exact (@lem3308801 A s y x' x h1 h2 (@lem3308793 A x)). Qed.
Lemma lem3308805 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term60 A s y x' x) (h2 : x' = x) : term78.
Proof. exact (fun h0 : ~ False => @lem3308804 A s y x' x h1 h2). Qed.
Lemma lem3308807 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3308808 : term78 = False.
Proof. exact (@lem3308807 False). Qed.
Lemma lem3308825 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3308826 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3308825 A x). Qed.
Lemma lem3308827 {A : Type'} (y : A) : y = y.
Proof. exact (@lem3308826 A y). Qed.
Lemma lem3308828 {A : Type'} (y : A) : term79 A y.
Proof. exact (fun h0 : term72 A y => @lem3308827 A y). Qed.
Lemma lem3308830 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3308831 {A : Type'} (y : A) : (term79 A y) = (y = y).
Proof. exact (@lem3308830 (y = y)). Qed.
Lemma lem3308832 {A : Type'} (y : A) : y = y.
Proof. exact (EQ_MP (@lem3308831 A y) (@lem3308828 A y)). Qed.
Lemma lem3308835 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3308837 {A : Type'} (y : A) : (term72 A y) = (term80 A y).
Proof. exact (@lem3308835 (y = y)). Qed.
Lemma lem3308840 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term60 A s y x' x) (h2 : x' = y) : term80 A y.
Proof. exact (EQ_MP (@lem3308837 A y) (@lem3308620 A s x x' y h1 h2)). Qed.
Lemma lem3308843 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term60 A s y x' x) (h2 : x' = y) : False.
Proof. exact (@lem3308840 A s x x' y h1 h2 (@lem3308832 A y)). Qed.
Lemma lem3308844 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term60 A s y x' x) (h2 : x' = y) : term78.
Proof. exact (fun h0 : ~ False => @lem3308843 A s x x' y h1 h2). Qed.
Lemma lem3308846 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3308847 : term78 = False.
Proof. exact (@lem3308846 False). Qed.
Lemma lem3308849 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term60 A s y x' x) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3308847) (@lem3308844 A s x x' y h1 h2)). Qed.
Lemma lem3308850 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term60 A s y x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3308808) (@lem3308805 A s y x' x h1 h2)). Qed.
Lemma lem3308851 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term63 A s y x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3308733) (@lem3308730 A s y x' x h1 h2)). Qed.
Lemma lem3308852 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term63 A s y x' x) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3308695) (@lem3308692 A s x x' y h1 h2)). Qed.
Lemma lem3308853 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term60 A s y x' x) (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3308849 A s x x' y h1 h2) (fun h3 : False => @lem3308408 A x' y h2)). Qed.
Lemma lem3308854 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term60 A s y x' x) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3308853 A s x x' y h1 h2) (@lem3308408 A x' y h2)). Qed.
Lemma lem3308855 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term60 A s y x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3308850 A s y x' x h1 h2) (fun h3 : False => @lem3308400 A x' x h2)). Qed.
Lemma lem3308856 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term60 A s y x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3308855 A s y x' x h1 h2) (@lem3308400 A x' x h2)). Qed.
Lemma lem3308857 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term68 A s x') (h2 : term60 A s y x' x) : (term68 A s x') = False.
Proof. exact (prop_ext (fun h3 : term68 A s x' => @lem3308771 A s y x' x h1 h2) (fun h3 : False => @lem3308392 A s x' h1)). Qed.
Lemma lem3308858 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term68 A s x') (h2 : term60 A s y x' x) : False.
Proof. exact (EQ_MP (@lem3308857 A s y x' x h1 h2) (@lem3308392 A s x' h1)). Qed.
Lemma lem3308859 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term63 A s y x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3308851 A s y x' x h1 h2) (fun h3 : False => @lem3308384 A x' x h2)). Qed.
Lemma lem3308860 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term63 A s y x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3308859 A s y x' x h1 h2) (@lem3308384 A x' x h2)). Qed.
Lemma lem3308861 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term63 A s y x' x) (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3308852 A s x x' y h1 h2) (fun h3 : False => @lem3308376 A x' y h2)). Qed.
Lemma lem3308862 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term63 A s y x' x) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3308861 A s x x' y h1 h2) (@lem3308376 A x' y h2)). Qed.
Lemma lem3308863 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term68 A s x') (h2 : term63 A s y x' x) : (term68 A s x') = False.
Proof. exact (prop_ext (fun h3 : term68 A s x' => @lem3308657 A s y x' x h1 h2) (fun h3 : False => @lem3308368 A s x' h1)). Qed.
Lemma lem3308864 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term68 A s x') (h2 : term63 A s y x' x) : False.
Proof. exact (EQ_MP (@lem3308863 A s y x' x h1 h2) (@lem3308368 A s x' h1)). Qed.
Lemma lem3308865 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term60 A s y x' x) (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3308854 A s x x' y h1 h2) (fun h3 : False => @lem3308360 A x' y h2)). Qed.
Lemma lem3308866 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term60 A s y x' x) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3308865 A s x x' y h1 h2) (@lem3308360 A x' y h2)). Qed.
Lemma lem3308867 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term60 A s y x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3308856 A s y x' x h1 h2) (fun h3 : False => @lem3308344 A x' x h2)). Qed.
Lemma lem3308868 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term60 A s y x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3308867 A s y x' x h1 h2) (@lem3308344 A x' x h2)). Qed.
Lemma lem3308869 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term68 A s x') (h2 : term60 A s y x' x) : (term68 A s x') = False.
Proof. exact (prop_ext (fun h3 : term68 A s x' => @lem3308858 A s y x' x h1 h2) (fun h3 : False => @lem3308328 A s x' h1)). Qed.
Lemma lem3308870 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term68 A s x') (h2 : term60 A s y x' x) : False.
Proof. exact (EQ_MP (@lem3308869 A s y x' x h1 h2) (@lem3308328 A s x' h1)). Qed.
Lemma lem3308871 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term63 A s y x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3308860 A s y x' x h1 h2) (fun h3 : False => @lem3308312 A x' x h2)). Qed.
Lemma lem3308872 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term63 A s y x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3308871 A s y x' x h1 h2) (@lem3308312 A x' x h2)). Qed.
Lemma lem3308873 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term63 A s y x' x) (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3308862 A s x x' y h1 h2) (fun h3 : False => @lem3308296 A x' y h2)). Qed.
Lemma lem3308874 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term63 A s y x' x) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3308873 A s x x' y h1 h2) (@lem3308296 A x' y h2)). Qed.
Lemma lem3308875 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term68 A s x') (h2 : term63 A s y x' x) : (term68 A s x') = False.
Proof. exact (prop_ext (fun h3 : term68 A s x' => @lem3308864 A s y x' x h1 h2) (fun h3 : False => @lem3308280 A s x' h1)). Qed.
Lemma lem3308876 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term68 A s x') (h2 : term63 A s y x' x) : False.
Proof. exact (EQ_MP (@lem3308875 A s y x' x h1 h2) (@lem3308280 A s x' h1)). Qed.
Lemma lem3308877 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term60 A s y x' x) (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3308866 A s x x' y h1 h2) (fun h3 : False => @lem3308360 A x' y h2)). Qed.
Lemma lem3308878 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term60 A s y x' x) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3308877 A s x x' y h1 h2) (@lem3308360 A x' y h2)). Qed.
Lemma lem3308879 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term60 A s y x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3308868 A s y x' x h1 h2) (fun h3 : False => @lem3308344 A x' x h2)). Qed.
Lemma lem3308880 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term60 A s y x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3308879 A s y x' x h1 h2) (@lem3308344 A x' x h2)). Qed.
Lemma lem3308881 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term68 A s x') (h2 : term60 A s y x' x) : (term68 A s x') = False.
Proof. exact (prop_ext (fun h3 : term68 A s x' => @lem3308870 A s y x' x h1 h2) (fun h3 : False => @lem3308328 A s x' h1)). Qed.
Lemma lem3308882 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term68 A s x') (h2 : term60 A s y x' x) : False.
Proof. exact (EQ_MP (@lem3308881 A s y x' x h1 h2) (@lem3308328 A s x' h1)). Qed.
Lemma lem3308883 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term63 A s y x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3308872 A s y x' x h1 h2) (fun h3 : False => @lem3308312 A x' x h2)). Qed.
Lemma lem3308884 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term63 A s y x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3308883 A s y x' x h1 h2) (@lem3308312 A x' x h2)). Qed.
Lemma lem3308885 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term63 A s y x' x) (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3308874 A s x x' y h1 h2) (fun h3 : False => @lem3308296 A x' y h2)). Qed.
Lemma lem3308886 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term63 A s y x' x) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3308885 A s x x' y h1 h2) (@lem3308296 A x' y h2)). Qed.
Lemma lem3308887 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term68 A s x') (h2 : term63 A s y x' x) : (term68 A s x') = False.
Proof. exact (prop_ext (fun h3 : term68 A s x' => @lem3308876 A s y x' x h1 h2) (fun h3 : False => @lem3308280 A s x' h1)). Qed.
Lemma lem3308888 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term68 A s x') (h2 : term63 A s y x' x) : False.
Proof. exact (EQ_MP (@lem3308887 A s y x' x h1 h2) (@lem3308280 A s x' h1)). Qed.
Lemma lem3308889 {A : Type'} (y : A) (s : A -> Prop) (x' : A) (x : A) (h1 : term60 A s y x' x) (h2 : term50 A s x' x) : False.
Proof. exact (or_elim (@lem3308261 A s x' x h2) (fun h0 : term68 A s x' => @lem3308882 A s y x' x h0 h1) (fun h0 : x' = x => @lem3308880 A s y x' x h1 h0)). Qed.
Lemma lem3308890 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term60 A s y x' x) : False.
Proof. exact (or_elim (@lem3308256 A s y x' x h1) (fun h0 : term50 A s x' x => @lem3308889 A y s x' x h1 h0) (fun h0 : x' = y => @lem3308878 A s x x' y h1 h0)). Qed.
Lemma lem3308891 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term63 A s y x' x) (h2 : term50 A s x' y) : False.
Proof. exact (or_elim (@lem3308251 A s x' y h2) (fun h0 : term68 A s x' => @lem3308888 A s y x' x h0 h1) (fun h0 : x' = y => @lem3308886 A s x x' y h1 h0)). Qed.
Lemma lem3308892 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term63 A s y x' x) : False.
Proof. exact (or_elim (@lem3308245 A s y x' x h1) (fun h0 : term50 A s x' y => @lem3308891 A x s x' y h1 h0) (fun h0 : x' = x => @lem3308884 A s y x' x h1 h0)). Qed.
Lemma lem3308893 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term46 A s y x' x) : False.
Proof. exact (or_elim (@lem3308242 A s y x' x h1) (fun h0 : term63 A s y x' x => @lem3308892 A s y x' x h0) (fun h0 : term60 A s y x' x => @lem3308890 A s y x' x h0)). Qed.
Lemma lem3308894 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term46 A s y x' x) : (term46 A s y x' x) = False.
Proof. exact (prop_ext (fun h2 : term46 A s y x' x => @lem3308893 A s y x' x h1) (fun h2 : False => @lem3308076 A s y x' x h1)). Qed.
Lemma lem3308895 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term46 A s y x' x) : False.
Proof. exact (EQ_MP (@lem3308894 A s y x' x h1) (@lem3308076 A s y x' x h1)). Qed.
Lemma lem3308896 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : term45 A s y x' x.
Proof. exact (fun h0 : term46 A s y x' x => @lem3308895 A s y x' x h0). Qed.
Lemma lem3308897 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term25 A s x x' y) = (term25 A s y x' x).
Proof. exact (EQ_MP (@lem3308075 A s y x' x) (@lem3308896 A s y x' x)). Qed.
Lemma lem3308902 {A : Type'} (s : A -> Prop) (y : A) (x : A) : term30 A s y x.
Proof. exact (fun x' : A => @lem3308897 A s y x' x). Qed.
Lemma lem3308907 {A : Type'} (y : A) (x : A) : term32 A y x.
Proof. exact (fun s : A -> Prop => @lem3308902 A s y x). Qed.
Lemma lem3308912 {A : Type'} (x : A) : term34 A x.
Proof. exact (fun y : A => @lem3308907 A y x). Qed.
Lemma lem3308917 {A : Type'} : term36 A.
Proof. exact (fun x : A => @lem3308912 A x). Qed.
Lemma lem3308918 {A : Type'} : term38 A.
Proof. exact (EQ_MP (@lem3308071 A) (@lem3308917 A)). Qed.
Lemma lem3308920 {A : Type'} : term38 A.
Proof. exact (@lem3307959 A (@lem3308918 A)). Qed.
Lemma lem3308921 {A : Type'} (h1 : term39 A) : False.
Proof. exact (@lem3308920 A (@lem3307943 A h1)). Qed.
Lemma lem3308922 {A : Type'} (h1 : term39 A) : (term39 A) = False.
Proof. exact (prop_ext (fun h2 : term39 A => @lem3308921 A h1) (fun h2 : False => @lem3307943 A h1)). Qed.
Lemma lem3308923 {A : Type'} (h1 : term39 A) : False.
Proof. exact (EQ_MP (@lem3308922 A h1) (@lem3307943 A h1)). Qed.
Lemma lem3308924 {A : Type'} : term38 A.
Proof. exact (fun h0 : term39 A => @lem3308923 A h0). Qed.
Lemma lem3308925 {A : Type'} : term36 A.
Proof. exact (EQ_MP (@lem3307942 A) (@lem3308924 A)). Qed.
Lemma lem3308926 {A : Type'} : term14 A.
Proof. exact (EQ_MP (@lem3307938 A) (@lem3308925 A)). Qed.
Lemma lem3308927 {A : Type'} : term13 A.
Proof. exact (EQ_MP (@lem3307818 A) (@lem3308926 A)). Qed.
