Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUBSET_INTER_ABSORPTION_term_abbrevs.
Require Import DISJ_ACI_spec.
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
Require Import thm17784_spec.
Require Import thm17930_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3256747 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3256748 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3256747 A s t). Qed.
Lemma lem3256755 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3256756 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1 A s t) = (term2 A s t).
Proof. exact (MK_COMB (@lem3256755) (@lem3256748 A s t)). Qed.
Lemma lem3256760 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term3 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3256761 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term3 A s t).
Proof. exact (@lem3256760 A s t). Qed.
Lemma lem3256762 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((@INTER A s t) = s) = (term4 A t s).
Proof. exact (@lem3256761 A (@INTER A s t) s). Qed.
Lemma lem3256771 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((@SUBSET A s t) = ((@INTER A s t) = s)) = ((term0 A s t) = (term4 A t s)).
Proof. exact (MK_COMB (@lem3256756 A s t) (@lem3256762 A t s)). Qed.
Lemma lem3256776 {A : Type'} (s : A -> Prop) : (term5 A s) = (term6 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3256771 A t s)). Qed.
Lemma lem3256777 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3256778 {A : Type'} (s : A -> Prop) : (term7 A s) = (term8 A s).
Proof. exact (MK_COMB (@lem3256777 A) (@lem3256776 A s)). Qed.
Lemma lem3256783 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3256778 A s)). Qed.
Lemma lem3256784 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3256785 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (MK_COMB (@lem3256784 A) (@lem3256783 A)). Qed.
Lemma lem3256790 {A : Type'} : (term12 A) = (term11 A).
Proof. exact (SYM (@lem3256785 A)). Qed.
Lemma lem3256808 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3256809 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3256808 A P x). Qed.
Lemma lem3256810 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3256809 A s x). Qed.
Lemma lem3256811 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3256812 {A : Type'} (s : A -> Prop) (x : A) : (term13 A x s) = (term14 A s x).
Proof. exact (MK_COMB (@lem3256811) (@lem3256810 A s x)). Qed.
Lemma lem3256814 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3256815 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3256814 A P x). Qed.
Lemma lem3256816 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3256815 A t x). Qed.
Lemma lem3256817 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term15 A s x t) = (term16 A s t x).
Proof. exact (MK_COMB (@lem3256812 A s x) (@lem3256816 A t x)). Qed.
Lemma lem3256820 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term17 A s t) = (term18 A s t).
Proof. exact (fun_ext (fun x : A => @lem3256817 A s t x)). Qed.
Lemma lem3256821 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3256822 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term0 A s t) = (term19 A s t).
Proof. exact (MK_COMB (@lem3256821 A) (@lem3256820 A s t)). Qed.
Lemma lem3256827 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3256828 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = (term20 A s t).
Proof. exact (MK_COMB (@lem3256827) (@lem3256822 A s t)). Qed.
Lemma lem3256836 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term21 A x s t) = (term22 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3256837 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term21 A x s t) = (term22 A s x t).
Proof. exact (@lem3256836 A s x t). Qed.
Lemma lem3256841 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3256842 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3256841 A P x). Qed.
Lemma lem3256843 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3256842 A s x). Qed.
Lemma lem3256844 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3256845 {A : Type'} (s : A -> Prop) (x : A) : (term23 A x s) = (term24 A s x).
Proof. exact (MK_COMB (@lem3256844) (@lem3256843 A s x)). Qed.
Lemma lem3256847 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3256848 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3256847 A P x). Qed.
Lemma lem3256849 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3256848 A t x). Qed.
Lemma lem3256850 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term22 A s x t) = (term25 A s t x).
Proof. exact (MK_COMB (@lem3256845 A s x) (@lem3256849 A t x)). Qed.
Lemma lem3256853 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term21 A x s t) = (term25 A s t x).
Proof. exact (TRANS (@lem3256837 A s x t) (@lem3256850 A s t x)). Qed.
Lemma lem3256854 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3256855 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term26 A x s t) = (term27 A s t x).
Proof. exact (MK_COMB (@lem3256854) (@lem3256853 A s t x)). Qed.
Lemma lem3256857 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3256858 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3256857 A P x). Qed.
Lemma lem3256859 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3256858 A s x). Qed.
Lemma lem3256860 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : ((term21 A x s t) = (@IN A x s)) = ((term25 A s t x) = (s x)).
Proof. exact (MK_COMB (@lem3256855 A s t x) (@lem3256859 A s x)). Qed.
Lemma lem3256863 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term28 A t s) = (term29 A t s).
Proof. exact (fun_ext (fun x : A => @lem3256860 A t s x)). Qed.
Lemma lem3256864 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3256865 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term4 A t s) = (term30 A t s).
Proof. exact (MK_COMB (@lem3256864 A) (@lem3256863 A t s)). Qed.
Lemma lem3256870 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term0 A s t) = (term4 A t s)) = ((term19 A s t) = (term30 A t s)).
Proof. exact (MK_COMB (@lem3256828 A s t) (@lem3256865 A t s)). Qed.
Lemma lem3256873 {A : Type'} (s : A -> Prop) : (term6 A s) = (term31 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3256870 A t s)). Qed.
Lemma lem3256874 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3256875 {A : Type'} (s : A -> Prop) : (term8 A s) = (term32 A s).
Proof. exact (MK_COMB (@lem3256874 A) (@lem3256873 A s)). Qed.
Lemma lem3256880 {A : Type'} : (term10 A) = (term33 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3256875 A s)). Qed.
Lemma lem3256881 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3256882 {A : Type'} : (term12 A) = (term34 A).
Proof. exact (MK_COMB (@lem3256881 A) (@lem3256880 A)). Qed.
Lemma lem3256887 {A : Type'} : (term34 A) = (term12 A).
Proof. exact (SYM (@lem3256882 A)). Qed.
Lemma lem3256889 (p : Prop) : p = (term35 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3256890 {A : Type'} : (term34 A) = (term36 A).
Proof. exact (@lem3256889 (term34 A)). Qed.
Lemma lem3256891 {A : Type'} : (term36 A) = (term34 A).
Proof. exact (SYM (@lem3256890 A)). Qed.
Lemma lem3256892 {A : Type'} (h1 : term37 A) : term37 A.
Proof. exact (h1). Qed.
Lemma lem3256895 {A : Type'} (h1 : term36 A) : term36 A.
Proof. exact (h1). Qed.
Lemma lem3256896 {A : Type'} : term38 A.
Proof. exact (fun h0 : term36 A => @lem3256895 A h0). Qed.
Lemma lem3256897 {A : Type'} (h1 : term38 A) : term38 A.
Proof. exact (h1). Qed.
Lemma lem3256898 {A : Type'} (h1 : term36 A) : term36 A.
Proof. exact (h1). Qed.
Lemma lem3256899 {A : Type'} (h1 : term36 A) (h2 : term38 A) : term36 A.
Proof. exact (@lem3256897 A h2 (@lem3256898 A h1)). Qed.
Lemma lem3256900 {A : Type'} (h1 : term36 A) : term39 A.
Proof. exact (fun h0 : term38 A => @lem3256899 A h1 h0). Qed.
Lemma lem3256901 {A : Type'} (h1 : term38 A) : term38 A.
Proof. exact (h1). Qed.
Lemma lem3256902 {A : Type'} (h1 : term36 A) (h2 : term38 A) : term36 A.
Proof. exact (@lem3256900 A h1 (@lem3256901 A h2)). Qed.
Lemma lem3256903 {A : Type'} (h1 : term38 A) : term38 A.
Proof. exact (fun h0 : term36 A => @lem3256902 A h0 h1). Qed.
Lemma lem3256904 {A : Type'} : term40 A.
Proof. exact (fun h0 : term38 A => @lem3256903 A h0). Qed.
Lemma lem3256907 {A : Type'} : term38 A.
Proof. exact (@lem3256904 A (@lem3256896 A)). Qed.
Lemma lem3256908 {A : Type'} : term38 A.
Proof. exact (@lem3256907 A). Qed.
Lemma lem3256910 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3256911 {A : Type'} : (term36 A) = (term41 A).
Proof. exact (@lem3256910 (term37 A)). Qed.
Lemma lem3256913 (t : Prop) : (term42 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3256914 {A : Type'} : (term41 A) = (term34 A).
Proof. exact (@lem3256913 (term34 A)). Qed.
Lemma lem3256939 {A : Type'} : (term36 A) = (term34 A).
Proof. exact (TRANS (@lem3256911 A) (@lem3256914 A)). Qed.
Lemma lem3256948 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : ((term25 A s t x) = (s x)) = ((term25 A s t x) = (s x)).
Proof. exact (eq_refl ((term25 A s t x) = (s x))). Qed.
Lemma lem3256949 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term29 A t s) = (term29 A t s).
Proof. exact (fun_ext (fun x : A => @lem3256948 A t s x)). Qed.
Lemma lem3256950 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3256951 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term30 A t s) = (term30 A t s).
Proof. exact (MK_COMB (@lem3256950 A) (@lem3256949 A t s)). Qed.
Lemma lem3256956 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term16 A s t x) = (term16 A s t x).
Proof. exact (eq_refl (term16 A s t x)). Qed.
Lemma lem3256957 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term18 A s t) = (term18 A s t).
Proof. exact (fun_ext (fun x : A => @lem3256956 A s t x)). Qed.
Lemma lem3256958 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3256959 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term19 A s t) = (term19 A s t).
Proof. exact (MK_COMB (@lem3256958 A) (@lem3256957 A s t)). Qed.
Lemma lem3256960 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3256961 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term20 A s t) = (term20 A s t).
Proof. exact (MK_COMB (@lem3256960) (@lem3256959 A s t)). Qed.
Lemma lem3256962 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term19 A s t) = (term30 A t s)) = ((term19 A s t) = (term30 A t s)).
Proof. exact (MK_COMB (@lem3256961 A s t) (@lem3256951 A t s)). Qed.
Lemma lem3256963 {A : Type'} (s : A -> Prop) : (term31 A s) = (term31 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3256962 A t s)). Qed.
Lemma lem3256964 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3256965 {A : Type'} (s : A -> Prop) : (term32 A s) = (term32 A s).
Proof. exact (MK_COMB (@lem3256964 A) (@lem3256963 A s)). Qed.
Lemma lem3256966 {A : Type'} : (term33 A) = (term33 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3256965 A s)). Qed.
Lemma lem3256967 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3256968 {A : Type'} : (term34 A) = (term34 A).
Proof. exact (MK_COMB (@lem3256967 A) (@lem3256966 A)). Qed.
Lemma lem3256999 {A : Type'} : (term36 A) = (term34 A).
Proof. exact (TRANS (@lem3256939 A) (@lem3256968 A)). Qed.
Lemma lem3257000 {A : Type'} : (term34 A) = (term36 A).
Proof. exact (SYM (@lem3256999 A)). Qed.
Lemma lem3257002 (p : Prop) : p = (term35 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3257003 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term19 A s t) = (term30 A t s)) = (term43 A t s).
Proof. exact (@lem3257002 ((term19 A s t) = (term30 A t s))). Qed.
Lemma lem3257004 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term43 A t s) = ((term19 A s t) = (term30 A t s)).
Proof. exact (SYM (@lem3257003 A t s)). Qed.
Lemma lem3257005 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term44 A t s) : term44 A t s.
Proof. exact (h1). Qed.
Lemma lem3257014 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term45 A s t x) = (term46 A s t x).
Proof. exact (@lem17362 (s x) (t x)). Qed.
Lemma lem3257019 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term16 A s t x) = (term47 A s t x).
Proof. exact (@lem17265 (s x) (t x)). Qed.
Lemma lem3257020 {A : Type'} (P : A -> Prop) : (term48 A P) = (term49 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3257021 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term50 A s t) = (term51 A s t).
Proof. exact (@lem3257020 A (term18 A s t)). Qed.
Lemma lem3257022 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term52 A s t x) = (term16 A s t x).
Proof. exact (eq_refl (term52 A s t x)). Qed.
Lemma lem3257023 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3257024 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term53 A s t x) = (term45 A s t x).
Proof. exact (MK_COMB (@lem3257023) (@lem3257022 A s t x)). Qed.
Lemma lem3257025 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term53 A s t x) = (term46 A s t x).
Proof. exact (TRANS (@lem3257024 A s t x) (@lem3257014 A s t x)). Qed.
Lemma lem3257026 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term54 A s t) = (term55 A s t).
Proof. exact (fun_ext (fun x : A => @lem3257025 A s t x)). Qed.
Lemma lem3257027 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3257028 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term51 A s t) = (term56 A s t).
Proof. exact (MK_COMB (@lem3257027 A) (@lem3257026 A s t)). Qed.
Lemma lem3257029 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term50 A s t) = (term56 A s t).
Proof. exact (TRANS (@lem3257021 A s t) (@lem3257028 A s t)). Qed.
Lemma lem3257030 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term18 A s t) = (term57 A s t).
Proof. exact (fun_ext (fun x : A => @lem3257019 A s t x)). Qed.
Lemma lem3257031 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3257032 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term19 A s t) = (term58 A s t).
Proof. exact (MK_COMB (@lem3257031 A) (@lem3257030 A s t)). Qed.
Lemma lem3257041 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term59 A s t x) = (term60 A s t x).
Proof. exact (@lem17045 (s x) (t x)). Qed.
Lemma lem3257045 {A : Type'} (s : A -> Prop) (x : A) : (term61 A s x) = (term61 A s x).
Proof. exact (eq_refl (term61 A s x)). Qed.
Lemma lem3257046 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3257047 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3257048 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term62 A s t x) = (term63 A s t x).
Proof. exact (MK_COMB (@lem3257047) (@lem3257041 A s t x)). Qed.
Lemma lem3257049 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term64 A t s x) = (term65 A t s x).
Proof. exact (MK_COMB (@lem3257048 A s t x) (@lem3257045 A s x)). Qed.
Lemma lem3257054 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term66 A t s x) = (term66 A t s x).
Proof. exact (eq_refl (term66 A t s x)). Qed.
Lemma lem3257055 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term67 A t s x) = (term68 A t s x).
Proof. exact (MK_COMB (@lem3257054 A t s x) (@lem3257049 A t s x)). Qed.
Lemma lem3257056 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term69 A t s x) = (term67 A t s x).
Proof. exact (@lem17930 (term25 A s t x) (s x)). Qed.
Lemma lem3257057 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term69 A t s x) = (term68 A t s x).
Proof. exact (TRANS (@lem3257056 A t s x) (@lem3257055 A t s x)). Qed.
Lemma lem3257058 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3257059 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term62 A s t x) = (term63 A s t x).
Proof. exact (MK_COMB (@lem3257058) (@lem3257041 A s t x)). Qed.
Lemma lem3257060 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term70 A t s x) = (term71 A t s x).
Proof. exact (MK_COMB (@lem3257059 A s t x) (@lem3257046 A s x)). Qed.
Lemma lem3257065 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term72 A t s x) = (term72 A t s x).
Proof. exact (eq_refl (term72 A t s x)). Qed.
Lemma lem3257066 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term73 A t s x) = (term74 A t s x).
Proof. exact (MK_COMB (@lem3257065 A t s x) (@lem3257060 A t s x)). Qed.
Lemma lem3257067 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : ((term25 A s t x) = (s x)) = (term73 A t s x).
Proof. exact (@lem17784 (term25 A s t x) (s x)). Qed.
Lemma lem3257068 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : ((term25 A s t x) = (s x)) = (term74 A t s x).
Proof. exact (TRANS (@lem3257067 A t s x) (@lem3257066 A t s x)). Qed.
Lemma lem3257069 {A : Type'} (P : A -> Prop) : (term48 A P) = (term49 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3257070 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term75 A t s) = (term76 A t s).
Proof. exact (@lem3257069 A (term29 A t s)). Qed.
Lemma lem3257071 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term77 A t s x) = ((term25 A s t x) = (s x)).
Proof. exact (eq_refl (term77 A t s x)). Qed.
Lemma lem3257072 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3257073 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term78 A t s x) = (term69 A t s x).
Proof. exact (MK_COMB (@lem3257072) (@lem3257071 A t s x)). Qed.
Lemma lem3257074 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term78 A t s x) = (term68 A t s x).
Proof. exact (TRANS (@lem3257073 A t s x) (@lem3257057 A t s x)). Qed.
Lemma lem3257075 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term79 A t s) = (term80 A t s).
Proof. exact (fun_ext (fun x : A => @lem3257074 A t s x)). Qed.
Lemma lem3257076 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3257077 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term76 A t s) = (term81 A t s).
Proof. exact (MK_COMB (@lem3257076 A) (@lem3257075 A t s)). Qed.
Lemma lem3257078 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term75 A t s) = (term81 A t s).
Proof. exact (TRANS (@lem3257070 A t s) (@lem3257077 A t s)). Qed.
Lemma lem3257079 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term29 A t s) = (term82 A t s).
Proof. exact (fun_ext (fun x : A => @lem3257068 A t s x)). Qed.
Lemma lem3257080 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3257081 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term30 A t s) = (term83 A t s).
Proof. exact (MK_COMB (@lem3257080 A) (@lem3257079 A t s)). Qed.
Lemma lem3257082 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3257083 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term84 A s t) = (term85 A s t).
Proof. exact (MK_COMB (@lem3257082) (@lem3257029 A s t)). Qed.
Lemma lem3257084 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term86 A t s) = (term87 A t s).
Proof. exact (MK_COMB (@lem3257083 A s t) (@lem3257081 A t s)). Qed.
Lemma lem3257085 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3257086 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term88 A s t) = (term89 A s t).
Proof. exact (MK_COMB (@lem3257085) (@lem3257032 A s t)). Qed.
Lemma lem3257087 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term90 A t s) = (term91 A t s).
Proof. exact (MK_COMB (@lem3257086 A s t) (@lem3257078 A t s)). Qed.
Lemma lem3257088 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3257089 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term92 A t s) = (term93 A t s).
Proof. exact (MK_COMB (@lem3257088) (@lem3257087 A t s)). Qed.
Lemma lem3257090 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term94 A t s) = (term95 A t s).
Proof. exact (MK_COMB (@lem3257089 A t s) (@lem3257084 A t s)). Qed.
Lemma lem3257091 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term44 A t s) = (term94 A t s).
Proof. exact (@lem17646 (term19 A s t) (term30 A t s)). Qed.
Lemma lem3257092 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term44 A t s) = (term95 A t s).
Proof. exact (TRANS (@lem3257091 A t s) (@lem3257090 A t s)). Qed.
Lemma lem3257202 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3257203 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (@lem3257202 A P Q). Qed.
Lemma lem3257204 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term98 A t s) = (term99 A t s).
Proof. exact (@lem3257203 A (term100 A t s) (term101 A t s)). Qed.
Lemma lem3257205 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term102 A t s x) = (term103 A t s x).
Proof. exact (eq_refl (term102 A t s x)). Qed.
Lemma lem3257206 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3257207 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term104 A t s x) = (term72 A t s x).
Proof. exact (MK_COMB (@lem3257206) (@lem3257205 A t s x)). Qed.
Lemma lem3257208 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term105 A t s x) = (term71 A t s x).
Proof. exact (eq_refl (term105 A t s x)). Qed.
Lemma lem3257209 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term106 A t s x) = (term74 A t s x).
Proof. exact (MK_COMB (@lem3257207 A t s x) (@lem3257208 A t s x)). Qed.
Lemma lem3257210 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term107 A t s) = (term82 A t s).
Proof. exact (fun_ext (fun x : A => @lem3257209 A t s x)). Qed.
Lemma lem3257211 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3257212 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term98 A t s) = (term83 A t s).
Proof. exact (MK_COMB (@lem3257211 A) (@lem3257210 A t s)). Qed.
Lemma lem3257213 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3257214 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term108 A t s) = (term109 A t s).
Proof. exact (MK_COMB (@lem3257213) (@lem3257212 A t s)). Qed.
Lemma lem3257215 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term102 A t s x) = (term103 A t s x).
Proof. exact (eq_refl (term102 A t s x)). Qed.
Lemma lem3257216 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term110 A t s) = (term100 A t s).
Proof. exact (fun_ext (fun x : A => @lem3257215 A t s x)). Qed.
Lemma lem3257217 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3257218 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term111 A t s) = (term112 A t s).
Proof. exact (MK_COMB (@lem3257217 A) (@lem3257216 A t s)). Qed.
Lemma lem3257219 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3257220 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term113 A t s) = (term114 A t s).
Proof. exact (MK_COMB (@lem3257219) (@lem3257218 A t s)). Qed.
Lemma lem3257221 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term105 A t s x) = (term71 A t s x).
Proof. exact (eq_refl (term105 A t s x)). Qed.
Lemma lem3257222 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term115 A t s) = (term101 A t s).
Proof. exact (fun_ext (fun x : A => @lem3257221 A t s x)). Qed.
Lemma lem3257223 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3257224 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term116 A t s) = (term117 A t s).
Proof. exact (MK_COMB (@lem3257223 A) (@lem3257222 A t s)). Qed.
Lemma lem3257225 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term99 A t s) = (term118 A t s).
Proof. exact (MK_COMB (@lem3257220 A t s) (@lem3257224 A t s)). Qed.
Lemma lem3257226 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term98 A t s) = (term99 A t s)) = ((term83 A t s) = (term118 A t s)).
Proof. exact (MK_COMB (@lem3257214 A t s) (@lem3257225 A t s)). Qed.
Lemma lem3257227 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term83 A t s) = (term118 A t s).
Proof. exact (EQ_MP (@lem3257226 A t s) (@lem3257204 A t s)). Qed.
Lemma lem3257308 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term85 A s t) = (term85 A s t).
Proof. exact (eq_refl (term85 A s t)). Qed.
Lemma lem3257309 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term87 A t s) = (term119 A t s).
Proof. exact (MK_COMB (@lem3257308 A s t) (@lem3257227 A t s)). Qed.
Lemma lem3257310 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term93 A t s) = (term93 A t s).
Proof. exact (eq_refl (term93 A t s)). Qed.
Lemma lem3257311 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term95 A t s) = (term120 A t s).
Proof. exact (MK_COMB (@lem3257310 A t s) (@lem3257309 A t s)). Qed.
Lemma lem3257313 {A : Type'} (P : Prop) (Q : A -> Prop) : (term121 A P Q) = (term122 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3257314 {A : Type'} (P : Prop) (Q : A -> Prop) : (term121 A P Q) = (term122 A P Q).
Proof. exact (@lem3257313 A P Q). Qed.
Lemma lem3257315 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term123 A t s) = (term124 A t s).
Proof. exact (@lem3257314 A (term58 A s t) (term80 A t s)). Qed.
Lemma lem3257316 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term125 A t s x) = (term68 A t s x).
Proof. exact (eq_refl (term125 A t s x)). Qed.
Lemma lem3257317 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term126 A t s) = (term80 A t s).
Proof. exact (fun_ext (fun x : A => @lem3257316 A t s x)). Qed.
Lemma lem3257318 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3257319 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term127 A t s) = (term81 A t s).
Proof. exact (MK_COMB (@lem3257318 A) (@lem3257317 A t s)). Qed.
Lemma lem3257320 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term89 A s t) = (term89 A s t).
Proof. exact (eq_refl (term89 A s t)). Qed.
Lemma lem3257321 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term123 A t s) = (term91 A t s).
Proof. exact (MK_COMB (@lem3257320 A s t) (@lem3257319 A t s)). Qed.
Lemma lem3257322 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3257323 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term128 A t s) = (term129 A t s).
Proof. exact (MK_COMB (@lem3257322) (@lem3257321 A t s)). Qed.
Lemma lem3257324 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term125 A t s x) = (term68 A t s x).
Proof. exact (eq_refl (term125 A t s x)). Qed.
Lemma lem3257325 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term89 A s t) = (term89 A s t).
Proof. exact (eq_refl (term89 A s t)). Qed.
Lemma lem3257326 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term130 A t s x) = (term131 A t s x).
Proof. exact (MK_COMB (@lem3257325 A s t) (@lem3257324 A t s x)). Qed.
Lemma lem3257327 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term132 A t s) = (term133 A t s).
Proof. exact (fun_ext (fun x : A => @lem3257326 A t s x)). Qed.
Lemma lem3257328 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3257329 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term124 A t s) = (term134 A t s).
Proof. exact (MK_COMB (@lem3257328 A) (@lem3257327 A t s)). Qed.
Lemma lem3257330 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term123 A t s) = (term124 A t s)) = ((term91 A t s) = (term134 A t s)).
Proof. exact (MK_COMB (@lem3257323 A t s) (@lem3257329 A t s)). Qed.
Lemma lem3257331 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term91 A t s) = (term134 A t s).
Proof. exact (EQ_MP (@lem3257330 A t s) (@lem3257315 A t s)). Qed.
Lemma lem3257332 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3257333 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term93 A t s) = (term135 A t s).
Proof. exact (MK_COMB (@lem3257332) (@lem3257331 A t s)). Qed.
Lemma lem3257335 {A : Type'} (P : A -> Prop) (Q : Prop) : (term136 A P Q) = (term137 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3257336 {A : Type'} (P : A -> Prop) (Q : Prop) : (term136 A P Q) = (term137 A P Q).
Proof. exact (@lem3257335 A P Q). Qed.
Lemma lem3257337 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term138 A t s) = (term139 A t s).
Proof. exact (@lem3257336 A (term55 A s t) (term118 A t s)). Qed.
Lemma lem3257338 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term140 A s t x) = (term46 A s t x).
Proof. exact (eq_refl (term140 A s t x)). Qed.
Lemma lem3257339 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term141 A s t) = (term55 A s t).
Proof. exact (fun_ext (fun x : A => @lem3257338 A s t x)). Qed.
Lemma lem3257340 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3257341 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term142 A s t) = (term56 A s t).
Proof. exact (MK_COMB (@lem3257340 A) (@lem3257339 A s t)). Qed.
Lemma lem3257342 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3257343 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term143 A s t) = (term85 A s t).
Proof. exact (MK_COMB (@lem3257342) (@lem3257341 A s t)). Qed.
Lemma lem3257344 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term118 A t s) = (term118 A t s).
Proof. exact (eq_refl (term118 A t s)). Qed.
Lemma lem3257345 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term138 A t s) = (term119 A t s).
Proof. exact (MK_COMB (@lem3257343 A s t) (@lem3257344 A t s)). Qed.
Lemma lem3257346 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3257347 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term144 A t s) = (term145 A t s).
Proof. exact (MK_COMB (@lem3257346) (@lem3257345 A t s)). Qed.
Lemma lem3257348 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term140 A s t x) = (term46 A s t x).
Proof. exact (eq_refl (term140 A s t x)). Qed.
Lemma lem3257349 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3257350 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term146 A s t x) = (term147 A s t x).
Proof. exact (MK_COMB (@lem3257349) (@lem3257348 A s t x)). Qed.
Lemma lem3257351 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term118 A t s) = (term118 A t s).
Proof. exact (eq_refl (term118 A t s)). Qed.
Lemma lem3257352 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term148 A x t s) = (term149 A x t s).
Proof. exact (MK_COMB (@lem3257350 A s t x) (@lem3257351 A t s)). Qed.
Lemma lem3257353 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term150 A t s) = (term151 A t s).
Proof. exact (fun_ext (fun x : A => @lem3257352 A x t s)). Qed.
Lemma lem3257354 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3257355 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term139 A t s) = (term152 A t s).
Proof. exact (MK_COMB (@lem3257354 A) (@lem3257353 A t s)). Qed.
Lemma lem3257356 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term138 A t s) = (term139 A t s)) = ((term119 A t s) = (term152 A t s)).
Proof. exact (MK_COMB (@lem3257347 A t s) (@lem3257355 A t s)). Qed.
Lemma lem3257357 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term119 A t s) = (term152 A t s).
Proof. exact (EQ_MP (@lem3257356 A t s) (@lem3257337 A t s)). Qed.
Lemma lem3257358 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term120 A t s) = (term153 A t s).
Proof. exact (MK_COMB (@lem3257333 A t s) (@lem3257357 A t s)). Qed.
Lemma lem3257360 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3257361 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (@lem3257360 A P Q). Qed.
Lemma lem3257362 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term156 A t s) = (term157 A t s).
Proof. exact (@lem3257361 A (term133 A t s) (term151 A t s)). Qed.
Lemma lem3257363 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term158 A t s x) = (term131 A t s x).
Proof. exact (eq_refl (term158 A t s x)). Qed.
Lemma lem3257364 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term159 A t s) = (term133 A t s).
Proof. exact (fun_ext (fun x : A => @lem3257363 A t s x)). Qed.
Lemma lem3257365 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3257366 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term160 A t s) = (term134 A t s).
Proof. exact (MK_COMB (@lem3257365 A) (@lem3257364 A t s)). Qed.
Lemma lem3257367 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3257368 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term161 A t s) = (term135 A t s).
Proof. exact (MK_COMB (@lem3257367) (@lem3257366 A t s)). Qed.
Lemma lem3257369 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term162 A t s x) = (term149 A x t s).
Proof. exact (eq_refl (term162 A t s x)). Qed.
Lemma lem3257370 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term163 A t s) = (term151 A t s).
Proof. exact (fun_ext (fun x : A => @lem3257369 A x t s)). Qed.
Lemma lem3257371 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3257372 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term164 A t s) = (term152 A t s).
Proof. exact (MK_COMB (@lem3257371 A) (@lem3257370 A t s)). Qed.
Lemma lem3257373 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term156 A t s) = (term153 A t s).
Proof. exact (MK_COMB (@lem3257368 A t s) (@lem3257372 A t s)). Qed.
Lemma lem3257374 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3257375 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term165 A t s) = (term166 A t s).
Proof. exact (MK_COMB (@lem3257374) (@lem3257373 A t s)). Qed.
Lemma lem3257376 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term158 A t s x) = (term131 A t s x).
Proof. exact (eq_refl (term158 A t s x)). Qed.
Lemma lem3257377 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3257378 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term167 A t s x) = (term168 A t s x).
Proof. exact (MK_COMB (@lem3257377) (@lem3257376 A t s x)). Qed.
Lemma lem3257379 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term162 A t s x) = (term149 A x t s).
Proof. exact (eq_refl (term162 A t s x)). Qed.
Lemma lem3257380 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term169 A t s x) = (term170 A x t s).
Proof. exact (MK_COMB (@lem3257378 A t s x) (@lem3257379 A x t s)). Qed.
Lemma lem3257381 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term171 A t s) = (term172 A t s).
Proof. exact (fun_ext (fun x : A => @lem3257380 A x t s)). Qed.
Lemma lem3257382 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3257383 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term157 A t s) = (term173 A t s).
Proof. exact (MK_COMB (@lem3257382 A) (@lem3257381 A t s)). Qed.
Lemma lem3257384 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term156 A t s) = (term157 A t s)) = ((term153 A t s) = (term173 A t s)).
Proof. exact (MK_COMB (@lem3257375 A t s) (@lem3257383 A t s)). Qed.
Lemma lem3257385 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term153 A t s) = (term173 A t s).
Proof. exact (EQ_MP (@lem3257384 A t s) (@lem3257362 A t s)). Qed.
Lemma lem3257386 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term120 A t s) = (term173 A t s).
Proof. exact (TRANS (@lem3257358 A t s) (@lem3257385 A t s)). Qed.
Lemma lem3257387 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term95 A t s) = (term173 A t s).
Proof. exact (TRANS (@lem3257311 A t s) (@lem3257386 A t s)). Qed.
Lemma lem3257388 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term44 A t s) = (term173 A t s).
Proof. exact (TRANS (@lem3257092 A t s) (@lem3257387 A t s)). Qed.
Lemma lem3257389 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term44 A t s) : term173 A t s.
Proof. exact (EQ_MP (@lem3257388 A t s) (@lem3257005 A t s h1)). Qed.
Lemma lem3257390 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term170 A x t s) : term170 A x t s.
Proof. exact (h1). Qed.
Lemma lem3257409 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term71 A t s x) = (term71 A t s x).
Proof. exact (eq_refl (term71 A t s x)). Qed.
Lemma lem3257410 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term101 A t s) = (term101 A t s).
Proof. exact (fun_ext (fun x : A => @lem3257409 A t s x)). Qed.
Lemma lem3257411 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3257412 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term117 A t s) = (term117 A t s).
Proof. exact (MK_COMB (@lem3257411 A) (@lem3257410 A t s)). Qed.
Lemma lem3257429 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term103 A t s x) = (term103 A t s x).
Proof. exact (eq_refl (term103 A t s x)). Qed.
Lemma lem3257430 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term100 A t s) = (term100 A t s).
Proof. exact (fun_ext (fun x : A => @lem3257429 A t s x)). Qed.
Lemma lem3257431 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3257432 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term112 A t s) = (term112 A t s).
Proof. exact (MK_COMB (@lem3257431 A) (@lem3257430 A t s)). Qed.
Lemma lem3257433 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3257434 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term114 A t s) = (term114 A t s).
Proof. exact (MK_COMB (@lem3257433) (@lem3257432 A t s)). Qed.
Lemma lem3257435 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term118 A t s) = (term118 A t s).
Proof. exact (MK_COMB (@lem3257434 A t s) (@lem3257412 A t s)). Qed.
Lemma lem3257448 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term147 A s t x) = (term147 A s t x).
Proof. exact (eq_refl (term147 A s t x)). Qed.
Lemma lem3257449 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term149 A x t s) = (term149 A x t s).
Proof. exact (MK_COMB (@lem3257448 A s t x) (@lem3257435 A t s)). Qed.
Lemma lem3257488 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term68 A t s x) = (term68 A t s x).
Proof. exact (eq_refl (term68 A t s x)). Qed.
Lemma lem3257499 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term47 A s t x) = (term47 A s t x).
Proof. exact (eq_refl (term47 A s t x)). Qed.
Lemma lem3257500 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term57 A s t) = (term57 A s t).
Proof. exact (fun_ext (fun x : A => @lem3257499 A s t x)). Qed.
Lemma lem3257501 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3257502 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term58 A s t) = (term58 A s t).
Proof. exact (MK_COMB (@lem3257501 A) (@lem3257500 A s t)). Qed.
Lemma lem3257503 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3257504 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term89 A s t) = (term89 A s t).
Proof. exact (MK_COMB (@lem3257503) (@lem3257502 A s t)). Qed.
Lemma lem3257505 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term131 A t s x) = (term131 A t s x).
Proof. exact (MK_COMB (@lem3257504 A s t) (@lem3257488 A t s x)). Qed.
Lemma lem3257506 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3257507 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term168 A t s x) = (term168 A t s x).
Proof. exact (MK_COMB (@lem3257506) (@lem3257505 A t s x)). Qed.
Lemma lem3257508 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term170 A x t s) = (term170 A x t s).
Proof. exact (MK_COMB (@lem3257507 A t s x) (@lem3257449 A x t s)). Qed.
Lemma lem3257509 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term170 A x t s) : term170 A x t s.
Proof. exact (EQ_MP (@lem3257508 A x t s) (@lem3257390 A x t s h1)). Qed.
Lemma lem3257510 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term131 A t s x) : term131 A t s x.
Proof. exact (h1). Qed.
Lemma lem3257511 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term149 A x t s) : term149 A x t s.
Proof. exact (h1). Qed.
Lemma lem3257512 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term131 A t s x) : term68 A t s x.
Proof. exact (proj2 (@lem3257510 A t s x h1)). Qed.
Lemma lem3257513 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term131 A t s x) : term58 A s t.
Proof. exact (proj1 (@lem3257510 A t s x h1)). Qed.
Lemma lem3257514 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term131 A t s x) : term65 A t s x.
Proof. exact (proj2 (@lem3257512 A t s x h1)). Qed.
Lemma lem3257515 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term131 A t s x) : term174 A t s x.
Proof. exact (proj1 (@lem3257512 A t s x h1)). Qed.
Lemma lem3257516 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term60 A s t x) : term60 A s t x.
Proof. exact (h1). Qed.
Lemma lem3257520 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term25 A s t x) : term25 A s t x.
Proof. exact (h1). Qed.
Lemma lem3257524 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term25 A s t x) : term25 A s t x.
Proof. exact (h1). Qed.
Lemma lem3257528 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term25 A s t x) : term25 A s t x.
Proof. exact (h1). Qed.
Lemma lem3257532 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term149 A x t s) : term118 A t s.
Proof. exact (proj2 (@lem3257511 A x t s h1)). Qed.
Lemma lem3257533 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term149 A x t s) : term46 A s t x.
Proof. exact (proj1 (@lem3257511 A x t s h1)). Qed.
Lemma lem3257535 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term149 A x t s) : term112 A t s.
Proof. exact (proj1 (@lem3257532 A x t s h1)). Qed.
Lemma lem3257554 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) : term61 A s x.
Proof. exact (h1). Qed.
Lemma lem3257579 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) : term61 A s x.
Proof. exact (h1). Qed.
Lemma lem3257583 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3257600 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) : term61 A t x.
Proof. exact (h1). Qed.
Lemma lem3257616 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term47 A s t x) = (term47 A s t x).
Proof. exact (eq_refl (term47 A s t x)). Qed.
Lemma lem3257617 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term57 A s t) = (term57 A s t).
Proof. exact (fun_ext (fun x : A => @lem3257616 A s t x)). Qed.
Lemma lem3257618 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3257620 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term58 A s t) = (term58 A s t).
Proof. exact (MK_COMB (@lem3257618 A) (@lem3257617 A s t)). Qed.
Lemma lem3257621 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term131 A t s x) : term58 A s t.
Proof. exact (EQ_MP (@lem3257620 A s t) (@lem3257513 A t s x h1)). Qed.
Lemma lem3257625 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) : term61 A t x.
Proof. exact (h1). Qed.
Lemma lem3257629 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3257646 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) : term61 A s x.
Proof. exact (h1). Qed.
Lemma lem3257671 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) : term61 A s x.
Proof. exact (h1). Qed.
Lemma lem3257675 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3257693 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term103 A t s x) = (term175 A t s x).
Proof. exact (@lem19699 (s x) (t x) (term61 A s x)). Qed.
Lemma lem3257694 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term100 A t s) = (term176 A t s).
Proof. exact (fun_ext (fun x : A => @lem3257693 A t s x)). Qed.
Lemma lem3257695 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3257697 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term112 A t s) = (term177 A t s).
Proof. exact (MK_COMB (@lem3257695 A) (@lem3257694 A t s)). Qed.
Lemma lem3257698 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term149 A x t s) : term177 A t s.
Proof. exact (EQ_MP (@lem3257697 A t s) (@lem3257535 A x t s h1)). Qed.
Lemma lem3257735 {A : Type'} (_33397 : A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term131 A t s x) : term178 A s t _33397.
Proof. exact (@lem3257621 A t s x h1 _33397). Qed.
Lemma lem3257736 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33397 : A) : (term178 A s t _33397) = (term47 A s t _33397).
Proof. exact (eq_refl (term178 A s t _33397)). Qed.
Lemma lem3257744 {A : Type'} (_33400 : A) (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term149 A x t s) : term179 A t s _33400.
Proof. exact (@lem3257698 A x t s h1 _33400). Qed.
Lemma lem3257745 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33400 : A) : (term179 A t s _33400) = (term175 A t s _33400).
Proof. exact (eq_refl (term179 A t s _33400)). Qed.
Lemma lem3257746 {A : Type'} (_33400 : A) (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term149 A x t s) : term175 A t s _33400.
Proof. exact (EQ_MP (@lem3257745 A t s _33400) (@lem3257744 A _33400 x t s h1)). Qed.
Lemma lem3257759 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) : term61 A s x.
Proof. exact (h1). Qed.
Lemma lem3257771 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) : term61 A s x.
Proof. exact (h1). Qed.
Lemma lem3257773 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3257781 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) : term61 A t x.
Proof. exact (h1). Qed.
Lemma lem3257791 {A : Type'} (_33397 : A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term131 A t s x) : term47 A s t _33397.
Proof. exact (EQ_MP (@lem3257736 A s t _33397) (@lem3257735 A _33397 t s x h1)). Qed.
Lemma lem3257793 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) : term61 A t x.
Proof. exact (h1). Qed.
Lemma lem3257795 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3257803 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) : term61 A s x.
Proof. exact (h1). Qed.
Lemma lem3257815 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) : term61 A s x.
Proof. exact (h1). Qed.
Lemma lem3257817 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3257833 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term149 A x t s) : term61 A t x.
Proof. exact (proj2 (@lem3257533 A x t s h1)). Qed.
Lemma lem3257845 {A : Type'} (_33400 : A) (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term149 A x t s) : term180 A t s _33400.
Proof. exact (proj2 (@lem3257746 A _33400 x t s h1)). Qed.
Lemma lem3257847 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term25 A s t x) : s x.
Proof. exact (proj1 (@lem3257520 A s t x h1)). Qed.
Lemma lem3257848 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term25 A s t x) : term181 A s x.
Proof. exact (fun h0 : term61 A s x => @lem3257847 A s t x h1). Qed.
Lemma lem3257850 (p : Prop) : (term182 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3257851 {A : Type'} (s : A -> Prop) (x : A) : (term181 A s x) = (s x).
Proof. exact (@lem3257850 (s x)). Qed.
Lemma lem3257852 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term25 A s t x) : s x.
Proof. exact (EQ_MP (@lem3257851 A s x) (@lem3257848 A s t x h1)). Qed.
Lemma lem3257855 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3257857 {A : Type'} (s : A -> Prop) (x : A) : (term61 A s x) = (term183 A s x).
Proof. exact (@lem3257855 (s x)). Qed.
Lemma lem3257860 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) : term183 A s x.
Proof. exact (EQ_MP (@lem3257857 A s x) (@lem3257759 A s x h1)). Qed.
Lemma lem3257863 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : term25 A s t x) : False.
Proof. exact (@lem3257860 A s x h1 (@lem3257852 A s t x h2)). Qed.
Lemma lem3257864 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : term25 A s t x) : term184.
Proof. exact (fun h0 : ~ False => @lem3257863 A s t x h1 h2). Qed.
Lemma lem3257866 (p : Prop) : (term182 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3257867 : term184 = False.
Proof. exact (@lem3257866 False). Qed.
Lemma lem3257868 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : term25 A s t x) : False.
Proof. exact (EQ_MP (@lem3257867) (@lem3257864 A s t x h1 h2)). Qed.
Lemma lem3257870 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3257871 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term181 A s x.
Proof. exact (fun h0 : term61 A s x => @lem3257870 A s x h1). Qed.
Lemma lem3257873 (p : Prop) : (term182 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3257874 {A : Type'} (s : A -> Prop) (x : A) : (term181 A s x) = (s x).
Proof. exact (@lem3257873 (s x)). Qed.
Lemma lem3257875 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3257874 A s x) (@lem3257871 A s x h1)). Qed.
Lemma lem3257878 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3257880 {A : Type'} (s : A -> Prop) (x : A) : (term61 A s x) = (term183 A s x).
Proof. exact (@lem3257878 (s x)). Qed.
Lemma lem3257883 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) : term183 A s x.
Proof. exact (EQ_MP (@lem3257880 A s x) (@lem3257771 A s x h1)). Qed.
Lemma lem3257886 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : False.
Proof. exact (@lem3257883 A s x h1 (@lem3257875 A s x h2)). Qed.
Lemma lem3257887 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : term184.
Proof. exact (fun h0 : ~ False => @lem3257886 A s x h1 h2). Qed.
Lemma lem3257889 (p : Prop) : (term182 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3257890 : term184 = False.
Proof. exact (@lem3257889 False). Qed.
Lemma lem3257891 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3257890) (@lem3257887 A s x h1 h2)). Qed.
Lemma lem3257893 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term25 A s t x) : t x.
Proof. exact (proj2 (@lem3257524 A s t x h1)). Qed.
Lemma lem3257894 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term25 A s t x) : term181 A t x.
Proof. exact (fun h0 : term61 A t x => @lem3257893 A s t x h1). Qed.
Lemma lem3257896 (p : Prop) : (term182 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3257897 {A : Type'} (t : A -> Prop) (x : A) : (term181 A t x) = (t x).
Proof. exact (@lem3257896 (t x)). Qed.
Lemma lem3257898 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term25 A s t x) : t x.
Proof. exact (EQ_MP (@lem3257897 A t x) (@lem3257894 A s t x h1)). Qed.
Lemma lem3257901 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3257903 {A : Type'} (t : A -> Prop) (x : A) : (term61 A t x) = (term183 A t x).
Proof. exact (@lem3257901 (t x)). Qed.
Lemma lem3257906 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) : term183 A t x.
Proof. exact (EQ_MP (@lem3257903 A t x) (@lem3257781 A t x h1)). Qed.
Lemma lem3257909 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : term25 A s t x) : False.
Proof. exact (@lem3257906 A t x h1 (@lem3257898 A s t x h2)). Qed.
Lemma lem3257910 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : term25 A s t x) : term184.
Proof. exact (fun h0 : ~ False => @lem3257909 A s t x h1 h2). Qed.
Lemma lem3257912 (p : Prop) : (term182 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3257913 : term184 = False.
Proof. exact (@lem3257912 False). Qed.
Lemma lem3257914 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : term25 A s t x) : False.
Proof. exact (EQ_MP (@lem3257913) (@lem3257910 A s t x h1 h2)). Qed.
Lemma lem3257916 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3257917 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term181 A s x.
Proof. exact (fun h0 : term61 A s x => @lem3257916 A s x h1). Qed.
Lemma lem3257919 (p : Prop) : (term182 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3257920 {A : Type'} (s : A -> Prop) (x : A) : (term181 A s x) = (s x).
Proof. exact (@lem3257919 (s x)). Qed.
Lemma lem3257921 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3257920 A s x) (@lem3257917 A s x h1)). Qed.
Lemma lem3257927 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3257928 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33397 : A) : (term47 A s t _33397) = (term180 A t s _33397).
Proof. exact (@lem3257927 (t _33397) (term61 A s _33397)). Qed.
Lemma lem3257934 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3257935 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33397 : A) : (term185 A s t _33397) = (term186 A t s _33397).
Proof. exact (MK_COMB (@lem3257934) (@lem3257928 A t s _33397)). Qed.
Lemma lem3257941 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33397 : A) : (term180 A t s _33397) = (term180 A t s _33397).
Proof. exact (eq_refl (term180 A t s _33397)). Qed.
Lemma lem3257942 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33397 : A) : ((term47 A s t _33397) = (term180 A t s _33397)) = ((term180 A t s _33397) = (term180 A t s _33397)).
Proof. exact (MK_COMB (@lem3257935 A t s _33397) (@lem3257941 A t s _33397)). Qed.
Lemma lem3257944 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3257945 (x : Prop) : (x = x) = True.
Proof. exact (@lem3257944 Prop x). Qed.
Lemma lem3257946 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33397 : A) : ((term180 A t s _33397) = (term180 A t s _33397)) = True.
Proof. exact (@lem3257945 (term180 A t s _33397)). Qed.
Lemma lem3257947 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33397 : A) : ((term47 A s t _33397) = (term180 A t s _33397)) = True.
Proof. exact (TRANS (@lem3257942 A t s _33397) (@lem3257946 A t s _33397)). Qed.
Lemma lem3257948 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33397 : A) : True = ((term47 A s t _33397) = (term180 A t s _33397)).
Proof. exact (SYM (@lem3257947 A t s _33397)). Qed.
Lemma lem3257949 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33397 : A) : (term47 A s t _33397) = (term180 A t s _33397).
Proof. exact (EQ_MP (@lem3257948 A t s _33397) (@lem0)). Qed.
Lemma lem3257950 {A : Type'} (_33397 : A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term131 A t s x) : term180 A t s _33397.
Proof. exact (EQ_MP (@lem3257949 A t s _33397) (@lem3257791 A _33397 t s x h1)). Qed.
Lemma lem3257952 (b : Prop) (a : Prop) : (a \/ b) = (term187 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3257953 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33397 : A) : (term180 A t s _33397) = (term188 A s t _33397).
Proof. exact (@lem3257952 (term61 A s _33397) (t _33397)). Qed.
Lemma lem3257955 (a : Prop) : (term42 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3257956 {A : Type'} (s : A -> Prop) (_33397 : A) : (term189 A s _33397) = (s _33397).
Proof. exact (@lem3257955 (s _33397)). Qed.
Lemma lem3257957 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3257958 {A : Type'} (s : A -> Prop) (_33397 : A) : (term190 A s _33397) = (term14 A s _33397).
Proof. exact (MK_COMB (@lem3257957) (@lem3257956 A s _33397)). Qed.
Lemma lem3257959 {A : Type'} (t : A -> Prop) (_33397 : A) : (t _33397) = (t _33397).
Proof. exact (eq_refl (t _33397)). Qed.
Lemma lem3257960 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33397 : A) : (term188 A s t _33397) = (term16 A s t _33397).
Proof. exact (MK_COMB (@lem3257958 A s _33397) (@lem3257959 A t _33397)). Qed.
Lemma lem3257961 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33397 : A) : (term180 A t s _33397) = (term16 A s t _33397).
Proof. exact (TRANS (@lem3257953 A s t _33397) (@lem3257960 A s t _33397)). Qed.
Lemma lem3257964 {A : Type'} (_33397 : A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term131 A t s x) : term16 A s t _33397.
Proof. exact (EQ_MP (@lem3257961 A s t _33397) (@lem3257950 A _33397 t s x h1)). Qed.
Lemma lem3257965 {A : Type'} (_33397 : A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term131 A t s x) : term16 A s t _33397.
Proof. exact (@lem3257964 A _33397 t s x h1). Qed.
Lemma lem3257966 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term131 A t s x) : term16 A s t x.
Proof. exact (@lem3257965 A x t s x h1). Qed.
Lemma lem3257969 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : s x) (h2 : term131 A t s x) : t x.
Proof. exact (@lem3257966 A t s x h2 (@lem3257921 A s x h1)). Qed.
Lemma lem3257970 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : s x) (h2 : term131 A t s x) : term181 A t x.
Proof. exact (fun h0 : term61 A t x => @lem3257969 A t s x h1 h2). Qed.
Lemma lem3257972 (p : Prop) : (term182 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3257973 {A : Type'} (t : A -> Prop) (x : A) : (term181 A t x) = (t x).
Proof. exact (@lem3257972 (t x)). Qed.
Lemma lem3257974 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : s x) (h2 : term131 A t s x) : t x.
Proof. exact (EQ_MP (@lem3257973 A t x) (@lem3257970 A t s x h1 h2)). Qed.
Lemma lem3257977 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3257979 {A : Type'} (t : A -> Prop) (x : A) : (term61 A t x) = (term183 A t x).
Proof. exact (@lem3257977 (t x)). Qed.
Lemma lem3257982 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) : term183 A t x.
Proof. exact (EQ_MP (@lem3257979 A t x) (@lem3257793 A t x h1)). Qed.
Lemma lem3257985 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A t s x) : False.
Proof. exact (@lem3257982 A t x h1 (@lem3257974 A t s x h2 h3)). Qed.
Lemma lem3257986 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A t s x) : term184.
Proof. exact (fun h0 : ~ False => @lem3257985 A t s x h1 h2 h3). Qed.
Lemma lem3257988 (p : Prop) : (term182 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3257989 : term184 = False.
Proof. exact (@lem3257988 False). Qed.
Lemma lem3257990 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A t s x) : False.
Proof. exact (EQ_MP (@lem3257989) (@lem3257986 A t s x h1 h2 h3)). Qed.
Lemma lem3257992 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term25 A s t x) : s x.
Proof. exact (proj1 (@lem3257528 A s t x h1)). Qed.
Lemma lem3257993 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term25 A s t x) : term181 A s x.
Proof. exact (fun h0 : term61 A s x => @lem3257992 A s t x h1). Qed.
Lemma lem3257995 (p : Prop) : (term182 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3257996 {A : Type'} (s : A -> Prop) (x : A) : (term181 A s x) = (s x).
Proof. exact (@lem3257995 (s x)). Qed.
Lemma lem3257997 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term25 A s t x) : s x.
Proof. exact (EQ_MP (@lem3257996 A s x) (@lem3257993 A s t x h1)). Qed.
Lemma lem3258000 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3258002 {A : Type'} (s : A -> Prop) (x : A) : (term61 A s x) = (term183 A s x).
Proof. exact (@lem3258000 (s x)). Qed.
Lemma lem3258005 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) : term183 A s x.
Proof. exact (EQ_MP (@lem3258002 A s x) (@lem3257803 A s x h1)). Qed.
Lemma lem3258008 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : term25 A s t x) : False.
Proof. exact (@lem3258005 A s x h1 (@lem3257997 A s t x h2)). Qed.
Lemma lem3258009 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : term25 A s t x) : term184.
Proof. exact (fun h0 : ~ False => @lem3258008 A s t x h1 h2). Qed.
Lemma lem3258011 (p : Prop) : (term182 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3258012 : term184 = False.
Proof. exact (@lem3258011 False). Qed.
Lemma lem3258013 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : term25 A s t x) : False.
Proof. exact (EQ_MP (@lem3258012) (@lem3258009 A s t x h1 h2)). Qed.
Lemma lem3258015 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3258016 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term181 A s x.
Proof. exact (fun h0 : term61 A s x => @lem3258015 A s x h1). Qed.
Lemma lem3258018 (p : Prop) : (term182 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3258019 {A : Type'} (s : A -> Prop) (x : A) : (term181 A s x) = (s x).
Proof. exact (@lem3258018 (s x)). Qed.
Lemma lem3258020 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3258019 A s x) (@lem3258016 A s x h1)). Qed.
Lemma lem3258023 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3258025 {A : Type'} (s : A -> Prop) (x : A) : (term61 A s x) = (term183 A s x).
Proof. exact (@lem3258023 (s x)). Qed.
Lemma lem3258028 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) : term183 A s x.
Proof. exact (EQ_MP (@lem3258025 A s x) (@lem3257815 A s x h1)). Qed.
Lemma lem3258031 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : False.
Proof. exact (@lem3258028 A s x h1 (@lem3258020 A s x h2)). Qed.
Lemma lem3258032 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : term184.
Proof. exact (fun h0 : ~ False => @lem3258031 A s x h1 h2). Qed.
Lemma lem3258034 (p : Prop) : (term182 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3258035 : term184 = False.
Proof. exact (@lem3258034 False). Qed.
Lemma lem3258036 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3258035) (@lem3258032 A s x h1 h2)). Qed.
Lemma lem3258038 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term149 A x t s) : s x.
Proof. exact (proj1 (@lem3257533 A x t s h1)). Qed.
Lemma lem3258039 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term149 A x t s) : term181 A s x.
Proof. exact (fun h0 : term61 A s x => @lem3258038 A x t s h1). Qed.
Lemma lem3258041 (p : Prop) : (term182 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3258042 {A : Type'} (s : A -> Prop) (x : A) : (term181 A s x) = (s x).
Proof. exact (@lem3258041 (s x)). Qed.
Lemma lem3258043 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term149 A x t s) : s x.
Proof. exact (EQ_MP (@lem3258042 A s x) (@lem3258039 A x t s h1)). Qed.
Lemma lem3258045 (b : Prop) (a : Prop) : (a \/ b) = (term187 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3258046 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33400 : A) : (term180 A t s _33400) = (term188 A s t _33400).
Proof. exact (@lem3258045 (term61 A s _33400) (t _33400)). Qed.
Lemma lem3258048 (a : Prop) : (term42 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3258049 {A : Type'} (s : A -> Prop) (_33400 : A) : (term189 A s _33400) = (s _33400).
Proof. exact (@lem3258048 (s _33400)). Qed.
Lemma lem3258050 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3258051 {A : Type'} (s : A -> Prop) (_33400 : A) : (term190 A s _33400) = (term14 A s _33400).
Proof. exact (MK_COMB (@lem3258050) (@lem3258049 A s _33400)). Qed.
Lemma lem3258052 {A : Type'} (t : A -> Prop) (_33400 : A) : (t _33400) = (t _33400).
Proof. exact (eq_refl (t _33400)). Qed.
Lemma lem3258053 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33400 : A) : (term188 A s t _33400) = (term16 A s t _33400).
Proof. exact (MK_COMB (@lem3258051 A s _33400) (@lem3258052 A t _33400)). Qed.
Lemma lem3258054 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33400 : A) : (term180 A t s _33400) = (term16 A s t _33400).
Proof. exact (TRANS (@lem3258046 A s t _33400) (@lem3258053 A s t _33400)). Qed.
Lemma lem3258057 {A : Type'} (_33400 : A) (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term149 A x t s) : term16 A s t _33400.
Proof. exact (EQ_MP (@lem3258054 A s t _33400) (@lem3257845 A _33400 x t s h1)). Qed.
Lemma lem3258058 {A : Type'} (_33400 : A) (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term149 A x t s) : term16 A s t _33400.
Proof. exact (@lem3258057 A _33400 x t s h1). Qed.
Lemma lem3258059 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term149 A x t s) : term16 A s t x.
Proof. exact (@lem3258058 A x x t s h1). Qed.
Lemma lem3258062 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term149 A x t s) : t x.
Proof. exact (@lem3258059 A x t s h1 (@lem3258043 A x t s h1)). Qed.
Lemma lem3258063 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term149 A x t s) : term181 A t x.
Proof. exact (fun h0 : term61 A t x => @lem3258062 A x t s h1). Qed.
Lemma lem3258065 (p : Prop) : (term182 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3258066 {A : Type'} (t : A -> Prop) (x : A) : (term181 A t x) = (t x).
Proof. exact (@lem3258065 (t x)). Qed.
Lemma lem3258067 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term149 A x t s) : t x.
Proof. exact (EQ_MP (@lem3258066 A t x) (@lem3258063 A x t s h1)). Qed.
Lemma lem3258070 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3258072 {A : Type'} (t : A -> Prop) (x : A) : (term61 A t x) = (term183 A t x).
Proof. exact (@lem3258070 (t x)). Qed.
Lemma lem3258075 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term149 A x t s) : term183 A t x.
Proof. exact (EQ_MP (@lem3258072 A t x) (@lem3257833 A x t s h1)). Qed.
Lemma lem3258078 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term149 A x t s) : False.
Proof. exact (@lem3258075 A x t s h1 (@lem3258067 A x t s h1)). Qed.
Lemma lem3258079 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term149 A x t s) : term184.
Proof. exact (fun h0 : ~ False => @lem3258078 A x t s h1). Qed.
Lemma lem3258081 (p : Prop) : (term182 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3258082 : term184 = False.
Proof. exact (@lem3258081 False). Qed.
Lemma lem3258083 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term149 A x t s) : False.
Proof. exact (EQ_MP (@lem3258082) (@lem3258079 A x t s h1)). Qed.
Lemma lem3258084 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3258036 A s x h1 h2) (fun h3 : False => @lem3257817 A s x h2)). Qed.
Lemma lem3258085 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3258084 A s x h1 h2) (@lem3257817 A s x h2)). Qed.
Lemma lem3258086 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : (term61 A s x) = False.
Proof. exact (prop_ext (fun h3 : term61 A s x => @lem3258085 A s x h1 h2) (fun h3 : False => @lem3257815 A s x h1)). Qed.
Lemma lem3258087 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3258086 A s x h1 h2) (@lem3257815 A s x h1)). Qed.
Lemma lem3258088 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : term25 A s t x) : (term61 A s x) = False.
Proof. exact (prop_ext (fun h3 : term61 A s x => @lem3258013 A s t x h1 h2) (fun h3 : False => @lem3257803 A s x h1)). Qed.
Lemma lem3258089 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : term25 A s t x) : False.
Proof. exact (EQ_MP (@lem3258088 A s t x h1 h2) (@lem3257803 A s x h1)). Qed.
Lemma lem3258090 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A t s x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3257990 A t s x h1 h2 h3) (fun h4 : False => @lem3257795 A s x h2)). Qed.
Lemma lem3258091 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A t s x) : False.
Proof. exact (EQ_MP (@lem3258090 A t s x h1 h2 h3) (@lem3257795 A s x h2)). Qed.
Lemma lem3258092 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A t s x) : (term61 A t x) = False.
Proof. exact (prop_ext (fun h4 : term61 A t x => @lem3258091 A t s x h1 h2 h3) (fun h4 : False => @lem3257793 A t x h1)). Qed.
Lemma lem3258093 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A t s x) : False.
Proof. exact (EQ_MP (@lem3258092 A t s x h1 h2 h3) (@lem3257793 A t x h1)). Qed.
Lemma lem3258094 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : term25 A s t x) : (term61 A t x) = False.
Proof. exact (prop_ext (fun h3 : term61 A t x => @lem3257914 A s t x h1 h2) (fun h3 : False => @lem3257781 A t x h1)). Qed.
Lemma lem3258095 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : term25 A s t x) : False.
Proof. exact (EQ_MP (@lem3258094 A s t x h1 h2) (@lem3257781 A t x h1)). Qed.
Lemma lem3258096 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3257891 A s x h1 h2) (fun h3 : False => @lem3257773 A s x h2)). Qed.
Lemma lem3258097 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3258096 A s x h1 h2) (@lem3257773 A s x h2)). Qed.
Lemma lem3258098 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : (term61 A s x) = False.
Proof. exact (prop_ext (fun h3 : term61 A s x => @lem3258097 A s x h1 h2) (fun h3 : False => @lem3257771 A s x h1)). Qed.
Lemma lem3258099 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3258098 A s x h1 h2) (@lem3257771 A s x h1)). Qed.
Lemma lem3258100 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : term25 A s t x) : (term61 A s x) = False.
Proof. exact (prop_ext (fun h3 : term61 A s x => @lem3257868 A s t x h1 h2) (fun h3 : False => @lem3257759 A s x h1)). Qed.
Lemma lem3258101 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : term25 A s t x) : False.
Proof. exact (EQ_MP (@lem3258100 A s t x h1 h2) (@lem3257759 A s x h1)). Qed.
Lemma lem3258102 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3258087 A s x h1 h2) (fun h3 : False => @lem3257675 A s x h2)). Qed.
Lemma lem3258103 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3258102 A s x h1 h2) (@lem3257675 A s x h2)). Qed.
Lemma lem3258104 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : (term61 A s x) = False.
Proof. exact (prop_ext (fun h3 : term61 A s x => @lem3258103 A s x h1 h2) (fun h3 : False => @lem3257671 A s x h1)). Qed.
Lemma lem3258105 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3258104 A s x h1 h2) (@lem3257671 A s x h1)). Qed.
Lemma lem3258106 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : term25 A s t x) : (term61 A s x) = False.
Proof. exact (prop_ext (fun h3 : term61 A s x => @lem3258089 A s t x h1 h2) (fun h3 : False => @lem3257646 A s x h1)). Qed.
Lemma lem3258107 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : term25 A s t x) : False.
Proof. exact (EQ_MP (@lem3258106 A s t x h1 h2) (@lem3257646 A s x h1)). Qed.
Lemma lem3258108 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A t s x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3258093 A t s x h1 h2 h3) (fun h4 : False => @lem3257629 A s x h2)). Qed.
Lemma lem3258109 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A t s x) : False.
Proof. exact (EQ_MP (@lem3258108 A t s x h1 h2 h3) (@lem3257629 A s x h2)). Qed.
Lemma lem3258110 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A t s x) : (term61 A t x) = False.
Proof. exact (prop_ext (fun h4 : term61 A t x => @lem3258109 A t s x h1 h2 h3) (fun h4 : False => @lem3257625 A t x h1)). Qed.
Lemma lem3258111 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A t s x) : False.
Proof. exact (EQ_MP (@lem3258110 A t s x h1 h2 h3) (@lem3257625 A t x h1)). Qed.
Lemma lem3258112 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : term25 A s t x) : (term61 A t x) = False.
Proof. exact (prop_ext (fun h3 : term61 A t x => @lem3258095 A s t x h1 h2) (fun h3 : False => @lem3257600 A t x h1)). Qed.
Lemma lem3258113 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : term25 A s t x) : False.
Proof. exact (EQ_MP (@lem3258112 A s t x h1 h2) (@lem3257600 A t x h1)). Qed.
Lemma lem3258114 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3258099 A s x h1 h2) (fun h3 : False => @lem3257583 A s x h2)). Qed.
Lemma lem3258115 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3258114 A s x h1 h2) (@lem3257583 A s x h2)). Qed.
Lemma lem3258116 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : (term61 A s x) = False.
Proof. exact (prop_ext (fun h3 : term61 A s x => @lem3258115 A s x h1 h2) (fun h3 : False => @lem3257579 A s x h1)). Qed.
Lemma lem3258117 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3258116 A s x h1 h2) (@lem3257579 A s x h1)). Qed.
Lemma lem3258118 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : term25 A s t x) : (term61 A s x) = False.
Proof. exact (prop_ext (fun h3 : term61 A s x => @lem3258101 A s t x h1 h2) (fun h3 : False => @lem3257554 A s x h1)). Qed.
Lemma lem3258119 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : term25 A s t x) : False.
Proof. exact (EQ_MP (@lem3258118 A s t x h1 h2) (@lem3257554 A s x h1)). Qed.
Lemma lem3258120 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3258105 A s x h1 h2) (fun h3 : False => @lem3257675 A s x h2)). Qed.
Lemma lem3258121 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3258120 A s x h1 h2) (@lem3257675 A s x h2)). Qed.
Lemma lem3258122 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : (term61 A s x) = False.
Proof. exact (prop_ext (fun h3 : term61 A s x => @lem3258121 A s x h1 h2) (fun h3 : False => @lem3257671 A s x h1)). Qed.
Lemma lem3258123 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3258122 A s x h1 h2) (@lem3257671 A s x h1)). Qed.
Lemma lem3258124 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : term25 A s t x) : (term61 A s x) = False.
Proof. exact (prop_ext (fun h3 : term61 A s x => @lem3258107 A s t x h1 h2) (fun h3 : False => @lem3257646 A s x h1)). Qed.
Lemma lem3258125 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : term25 A s t x) : False.
Proof. exact (EQ_MP (@lem3258124 A s t x h1 h2) (@lem3257646 A s x h1)). Qed.
Lemma lem3258126 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A t s x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3258111 A t s x h1 h2 h3) (fun h4 : False => @lem3257629 A s x h2)). Qed.
Lemma lem3258127 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A t s x) : False.
Proof. exact (EQ_MP (@lem3258126 A t s x h1 h2 h3) (@lem3257629 A s x h2)). Qed.
Lemma lem3258128 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A t s x) : (term61 A t x) = False.
Proof. exact (prop_ext (fun h4 : term61 A t x => @lem3258127 A t s x h1 h2 h3) (fun h4 : False => @lem3257625 A t x h1)). Qed.
Lemma lem3258129 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A t s x) : False.
Proof. exact (EQ_MP (@lem3258128 A t s x h1 h2 h3) (@lem3257625 A t x h1)). Qed.
Lemma lem3258130 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : term25 A s t x) : (term61 A t x) = False.
Proof. exact (prop_ext (fun h3 : term61 A t x => @lem3258113 A s t x h1 h2) (fun h3 : False => @lem3257600 A t x h1)). Qed.
Lemma lem3258131 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : term25 A s t x) : False.
Proof. exact (EQ_MP (@lem3258130 A s t x h1 h2) (@lem3257600 A t x h1)). Qed.
Lemma lem3258132 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3258117 A s x h1 h2) (fun h3 : False => @lem3257583 A s x h2)). Qed.
Lemma lem3258133 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3258132 A s x h1 h2) (@lem3257583 A s x h2)). Qed.
Lemma lem3258134 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : (term61 A s x) = False.
Proof. exact (prop_ext (fun h3 : term61 A s x => @lem3258133 A s x h1 h2) (fun h3 : False => @lem3257579 A s x h1)). Qed.
Lemma lem3258135 {A : Type'} (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3258134 A s x h1 h2) (@lem3257579 A s x h1)). Qed.
Lemma lem3258136 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : term25 A s t x) : (term61 A s x) = False.
Proof. exact (prop_ext (fun h3 : term61 A s x => @lem3258119 A s t x h1 h2) (fun h3 : False => @lem3257554 A s x h1)). Qed.
Lemma lem3258137 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : term25 A s t x) : False.
Proof. exact (EQ_MP (@lem3258136 A s t x h1 h2) (@lem3257554 A s x h1)). Qed.
Lemma lem3258138 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : term131 A t s x) : False.
Proof. exact (or_elim (@lem3257515 A t s x h2) (fun h0 : term25 A s t x => @lem3258125 A s t x h1 h0) (fun h0 : s x => @lem3258123 A s x h1 h0)). Qed.
Lemma lem3258139 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : term131 A t s x) : False.
Proof. exact (or_elim (@lem3257515 A t s x h2) (fun h0 : term25 A s t x => @lem3258131 A s t x h1 h0) (fun h0 : s x => @lem3258129 A t s x h1 h0 h2)). Qed.
Lemma lem3258140 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term61 A s x) (h2 : term131 A t s x) : False.
Proof. exact (or_elim (@lem3257515 A t s x h2) (fun h0 : term25 A s t x => @lem3258137 A s t x h1 h0) (fun h0 : s x => @lem3258135 A s x h1 h0)). Qed.
Lemma lem3258141 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term131 A t s x) (h2 : term60 A s t x) : False.
Proof. exact (or_elim (@lem3257516 A s t x h2) (fun h0 : term61 A s x => @lem3258140 A t s x h0 h1) (fun h0 : term61 A t x => @lem3258139 A t s x h0 h1)). Qed.
Lemma lem3258142 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term131 A t s x) : False.
Proof. exact (or_elim (@lem3257514 A t s x h1) (fun h0 : term60 A s t x => @lem3258141 A s t x h1 h0) (fun h0 : term61 A s x => @lem3258138 A t s x h0 h1)). Qed.
Lemma lem3258143 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term170 A x t s) : False.
Proof. exact (or_elim (@lem3257509 A x t s h1) (fun h0 : term131 A t s x => @lem3258142 A t s x h0) (fun h0 : term149 A x t s => @lem3258083 A x t s h0)). Qed.
Lemma lem3258144 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term170 A x t s) : (term170 A x t s) = False.
Proof. exact (prop_ext (fun h2 : term170 A x t s => @lem3258143 A x t s h1) (fun h2 : False => @lem3257509 A x t s h1)). Qed.
Lemma lem3258145 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term170 A x t s) : False.
Proof. exact (EQ_MP (@lem3258144 A x t s h1) (@lem3257509 A x t s h1)). Qed.
Lemma lem3258146 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term44 A t s) : False.
Proof. exact (ex_elim (@lem3257389 A t s h1) (fun x : A => fun h0 : term172 A t s x => @lem3258145 A x t s h0)). Qed.
Lemma lem3258147 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term44 A t s) : (term44 A t s) = False.
Proof. exact (prop_ext (fun h2 : term44 A t s => @lem3258146 A t s h1) (fun h2 : False => @lem3257005 A t s h1)). Qed.
Lemma lem3258148 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term44 A t s) : False.
Proof. exact (EQ_MP (@lem3258147 A t s h1) (@lem3257005 A t s h1)). Qed.
Lemma lem3258149 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term43 A t s.
Proof. exact (fun h0 : term44 A t s => @lem3258148 A t s h0). Qed.
Lemma lem3258150 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term19 A s t) = (term30 A t s).
Proof. exact (EQ_MP (@lem3257004 A t s) (@lem3258149 A t s)). Qed.
Lemma lem3258155 {A : Type'} (s : A -> Prop) : term32 A s.
Proof. exact (fun t : A -> Prop => @lem3258150 A t s). Qed.
Lemma lem3258160 {A : Type'} : term34 A.
Proof. exact (fun s : A -> Prop => @lem3258155 A s). Qed.
Lemma lem3258161 {A : Type'} : term36 A.
Proof. exact (EQ_MP (@lem3257000 A) (@lem3258160 A)). Qed.
Lemma lem3258163 {A : Type'} : term36 A.
Proof. exact (@lem3256908 A (@lem3258161 A)). Qed.
Lemma lem3258164 {A : Type'} (h1 : term37 A) : False.
Proof. exact (@lem3258163 A (@lem3256892 A h1)). Qed.
Lemma lem3258165 {A : Type'} (h1 : term37 A) : (term37 A) = False.
Proof. exact (prop_ext (fun h2 : term37 A => @lem3258164 A h1) (fun h2 : False => @lem3256892 A h1)). Qed.
Lemma lem3258166 {A : Type'} (h1 : term37 A) : False.
Proof. exact (EQ_MP (@lem3258165 A h1) (@lem3256892 A h1)). Qed.
Lemma lem3258167 {A : Type'} : term36 A.
Proof. exact (fun h0 : term37 A => @lem3258166 A h0). Qed.
Lemma lem3258168 {A : Type'} : term34 A.
Proof. exact (EQ_MP (@lem3256891 A) (@lem3258167 A)). Qed.
Lemma lem3258169 {A : Type'} : term12 A.
Proof. exact (EQ_MP (@lem3256887 A) (@lem3258168 A)). Qed.
Lemma lem3258170 {A : Type'} : term11 A.
Proof. exact (EQ_MP (@lem3256790 A) (@lem3258169 A)). Qed.
