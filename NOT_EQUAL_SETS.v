Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NOT_EQUAL_SETS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17500_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm17930_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19490_spec.
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
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3211784 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3211785 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3211784 A s t). Qed.
Lemma lem3211794 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3211795 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1 A s t) = (term2 A s t).
Proof. exact (MK_COMB (@lem3211794) (@lem3211785 A s t)). Qed.
Lemma lem3211796 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3211797 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term3 A s t) = (term4 A s t).
Proof. exact (MK_COMB (@lem3211796) (@lem3211795 A s t)). Qed.
Lemma lem3211806 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term5 A t s) = (term5 A t s).
Proof. exact (eq_refl (term5 A t s)). Qed.
Lemma lem3211807 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term1 A s t) = (term5 A t s)) = ((term2 A s t) = (term5 A t s)).
Proof. exact (MK_COMB (@lem3211797 A s t) (@lem3211806 A t s)). Qed.
Lemma lem3211812 {A : Type'} (s : A -> Prop) : (term6 A s) = (term7 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3211807 A t s)). Qed.
Lemma lem3211813 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3211814 {A : Type'} (s : A -> Prop) : (term8 A s) = (term9 A s).
Proof. exact (MK_COMB (@lem3211813 A) (@lem3211812 A s)). Qed.
Lemma lem3211819 {A : Type'} : (term10 A) = (term11 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3211814 A s)). Qed.
Lemma lem3211820 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3211821 {A : Type'} : (term12 A) = (term13 A).
Proof. exact (MK_COMB (@lem3211820 A) (@lem3211819 A)). Qed.
Lemma lem3211826 {A : Type'} : (term13 A) = (term12 A).
Proof. exact (SYM (@lem3211821 A)). Qed.
Lemma lem3211844 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3211845 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3211844 A P x). Qed.
Lemma lem3211846 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3211845 A s x). Qed.
Lemma lem3211847 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3211848 {A : Type'} (s : A -> Prop) (x : A) : (term14 A x s) = (term15 A s x).
Proof. exact (MK_COMB (@lem3211847) (@lem3211846 A s x)). Qed.
Lemma lem3211850 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3211851 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3211850 A P x). Qed.
Lemma lem3211852 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3211851 A t x). Qed.
Lemma lem3211853 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x t)) = ((s x) = (t x)).
Proof. exact (MK_COMB (@lem3211848 A s x) (@lem3211852 A t x)). Qed.
Lemma lem3211856 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term16 A s t) = (term17 A s t).
Proof. exact (fun_ext (fun x : A => @lem3211853 A s t x)). Qed.
Lemma lem3211857 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3211858 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term0 A s t) = (term18 A s t).
Proof. exact (MK_COMB (@lem3211857 A) (@lem3211856 A s t)). Qed.
Lemma lem3211863 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3211864 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = (term19 A s t).
Proof. exact (MK_COMB (@lem3211863) (@lem3211858 A s t)). Qed.
Lemma lem3211865 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3211866 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term4 A s t) = (term20 A s t).
Proof. exact (MK_COMB (@lem3211865) (@lem3211864 A s t)). Qed.
Lemma lem3211874 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3211875 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3211874 A P x). Qed.
Lemma lem3211876 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3211875 A t x). Qed.
Lemma lem3211877 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3211878 {A : Type'} (t : A -> Prop) (x : A) : (term14 A x t) = (term15 A t x).
Proof. exact (MK_COMB (@lem3211877) (@lem3211876 A t x)). Qed.
Lemma lem3211880 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3211881 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3211880 A P x). Qed.
Lemma lem3211882 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3211881 A s x). Qed.
Lemma lem3211883 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3211884 {A : Type'} (s : A -> Prop) (x : A) : (term21 A x s) = (term22 A s x).
Proof. exact (MK_COMB (@lem3211883) (@lem3211882 A s x)). Qed.
Lemma lem3211885 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : ((@IN A x t) = (term21 A x s)) = ((t x) = (term22 A s x)).
Proof. exact (MK_COMB (@lem3211878 A t x) (@lem3211884 A s x)). Qed.
Lemma lem3211888 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term23 A t s) = (term24 A t s).
Proof. exact (fun_ext (fun x : A => @lem3211885 A t s x)). Qed.
Lemma lem3211889 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3211890 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term5 A t s) = (term25 A t s).
Proof. exact (MK_COMB (@lem3211889 A) (@lem3211888 A t s)). Qed.
Lemma lem3211895 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term2 A s t) = (term5 A t s)) = ((term19 A s t) = (term25 A t s)).
Proof. exact (MK_COMB (@lem3211866 A s t) (@lem3211890 A t s)). Qed.
Lemma lem3211898 {A : Type'} (s : A -> Prop) : (term7 A s) = (term26 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3211895 A t s)). Qed.
Lemma lem3211899 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3211900 {A : Type'} (s : A -> Prop) : (term9 A s) = (term27 A s).
Proof. exact (MK_COMB (@lem3211899 A) (@lem3211898 A s)). Qed.
Lemma lem3211905 {A : Type'} : (term11 A) = (term28 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3211900 A s)). Qed.
Lemma lem3211906 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3211907 {A : Type'} : (term13 A) = (term29 A).
Proof. exact (MK_COMB (@lem3211906 A) (@lem3211905 A)). Qed.
Lemma lem3211912 {A : Type'} : (term29 A) = (term13 A).
Proof. exact (SYM (@lem3211907 A)). Qed.
Lemma lem3211914 (p : Prop) : p = (term30 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3211915 {A : Type'} : (term29 A) = (term31 A).
Proof. exact (@lem3211914 (term29 A)). Qed.
Lemma lem3211916 {A : Type'} : (term31 A) = (term29 A).
Proof. exact (SYM (@lem3211915 A)). Qed.
Lemma lem3211917 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem3211920 {A : Type'} (h1 : term31 A) : term31 A.
Proof. exact (h1). Qed.
Lemma lem3211921 {A : Type'} : term33 A.
Proof. exact (fun h0 : term31 A => @lem3211920 A h0). Qed.
Lemma lem3211922 {A : Type'} (h1 : term33 A) : term33 A.
Proof. exact (h1). Qed.
Lemma lem3211923 {A : Type'} (h1 : term31 A) : term31 A.
Proof. exact (h1). Qed.
Lemma lem3211924 {A : Type'} (h1 : term31 A) (h2 : term33 A) : term31 A.
Proof. exact (@lem3211922 A h2 (@lem3211923 A h1)). Qed.
Lemma lem3211925 {A : Type'} (h1 : term31 A) : term34 A.
Proof. exact (fun h0 : term33 A => @lem3211924 A h1 h0). Qed.
Lemma lem3211926 {A : Type'} (h1 : term33 A) : term33 A.
Proof. exact (h1). Qed.
Lemma lem3211927 {A : Type'} (h1 : term31 A) (h2 : term33 A) : term31 A.
Proof. exact (@lem3211925 A h1 (@lem3211926 A h2)). Qed.
Lemma lem3211928 {A : Type'} (h1 : term33 A) : term33 A.
Proof. exact (fun h0 : term31 A => @lem3211927 A h0 h1). Qed.
Lemma lem3211929 {A : Type'} : term35 A.
Proof. exact (fun h0 : term33 A => @lem3211928 A h0). Qed.
Lemma lem3211932 {A : Type'} : term33 A.
Proof. exact (@lem3211929 A (@lem3211921 A)). Qed.
Lemma lem3211933 {A : Type'} : term33 A.
Proof. exact (@lem3211932 A). Qed.
Lemma lem3211935 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3211936 {A : Type'} : (term31 A) = (term36 A).
Proof. exact (@lem3211935 (term32 A)). Qed.
Lemma lem3211938 (t : Prop) : (term37 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3211939 {A : Type'} : (term36 A) = (term29 A).
Proof. exact (@lem3211938 (term29 A)). Qed.
Lemma lem3211960 {A : Type'} : (term31 A) = (term29 A).
Proof. exact (TRANS (@lem3211936 A) (@lem3211939 A)). Qed.
Lemma lem3211967 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : ((t x) = (term22 A s x)) = ((t x) = (term22 A s x)).
Proof. exact (eq_refl ((t x) = (term22 A s x))). Qed.
Lemma lem3211968 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term24 A t s) = (term24 A t s).
Proof. exact (fun_ext (fun x : A => @lem3211967 A t s x)). Qed.
Lemma lem3211969 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3211970 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term25 A t s) = (term25 A t s).
Proof. exact (MK_COMB (@lem3211969 A) (@lem3211968 A t s)). Qed.
Lemma lem3211975 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((s x) = (t x)) = ((s x) = (t x)).
Proof. exact (eq_refl ((s x) = (t x))). Qed.
Lemma lem3211976 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term17 A s t) = (term17 A s t).
Proof. exact (fun_ext (fun x : A => @lem3211975 A s t x)). Qed.
Lemma lem3211977 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3211978 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term18 A s t) = (term18 A s t).
Proof. exact (MK_COMB (@lem3211977 A) (@lem3211976 A s t)). Qed.
Lemma lem3211979 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3211980 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term19 A s t) = (term19 A s t).
Proof. exact (MK_COMB (@lem3211979) (@lem3211978 A s t)). Qed.
Lemma lem3211981 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3211982 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term20 A s t) = (term20 A s t).
Proof. exact (MK_COMB (@lem3211981) (@lem3211980 A s t)). Qed.
Lemma lem3211983 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term19 A s t) = (term25 A t s)) = ((term19 A s t) = (term25 A t s)).
Proof. exact (MK_COMB (@lem3211982 A s t) (@lem3211970 A t s)). Qed.
Lemma lem3211984 {A : Type'} (s : A -> Prop) : (term26 A s) = (term26 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3211983 A t s)). Qed.
Lemma lem3211985 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3211986 {A : Type'} (s : A -> Prop) : (term27 A s) = (term27 A s).
Proof. exact (MK_COMB (@lem3211985 A) (@lem3211984 A s)). Qed.
Lemma lem3211987 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3211986 A s)). Qed.
Lemma lem3211988 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3211989 {A : Type'} : (term29 A) = (term29 A).
Proof. exact (MK_COMB (@lem3211988 A) (@lem3211987 A)). Qed.
Lemma lem3212016 {A : Type'} : (term31 A) = (term29 A).
Proof. exact (TRANS (@lem3211960 A) (@lem3211989 A)). Qed.
Lemma lem3212017 {A : Type'} : (term29 A) = (term31 A).
Proof. exact (SYM (@lem3212016 A)). Qed.
Lemma lem3212019 (p : Prop) : p = (term30 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3212020 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term19 A s t) = (term25 A t s)) = (term38 A t s).
Proof. exact (@lem3212019 ((term19 A s t) = (term25 A t s))). Qed.
Lemma lem3212021 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term38 A t s) = ((term19 A s t) = (term25 A t s)).
Proof. exact (SYM (@lem3212020 A t s)). Qed.
Lemma lem3212022 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term39 A t s) : term39 A t s.
Proof. exact (h1). Qed.
Lemma lem3212037 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term40 A s t x) = (term41 A s t x).
Proof. exact (@lem17930 (s x) (t x)). Qed.
Lemma lem3212048 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((s x) = (t x)) = (term42 A s t x).
Proof. exact (@lem17784 (s x) (t x)). Qed.
Lemma lem3212049 {A : Type'} (P : A -> Prop) : (term43 A P) = (term44 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3212050 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term19 A s t) = (term45 A s t).
Proof. exact (@lem3212049 A (term17 A s t)). Qed.
Lemma lem3212051 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term46 A s t x) = ((s x) = (t x)).
Proof. exact (eq_refl (term46 A s t x)). Qed.
Lemma lem3212052 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3212053 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term47 A s t x) = (term40 A s t x).
Proof. exact (MK_COMB (@lem3212052) (@lem3212051 A s t x)). Qed.
Lemma lem3212054 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term47 A s t x) = (term41 A s t x).
Proof. exact (TRANS (@lem3212053 A s t x) (@lem3212037 A s t x)). Qed.
Lemma lem3212055 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term48 A s t) = (term49 A s t).
Proof. exact (fun_ext (fun x : A => @lem3212054 A s t x)). Qed.
Lemma lem3212056 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3212057 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term45 A s t) = (term50 A s t).
Proof. exact (MK_COMB (@lem3212056 A) (@lem3212055 A s t)). Qed.
Lemma lem3212058 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term19 A s t) = (term50 A s t).
Proof. exact (TRANS (@lem3212050 A s t) (@lem3212057 A s t)). Qed.
Lemma lem3212059 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term17 A s t) = (term51 A s t).
Proof. exact (fun_ext (fun x : A => @lem3212048 A s t x)). Qed.
Lemma lem3212060 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3212061 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term18 A s t) = (term52 A s t).
Proof. exact (MK_COMB (@lem3212060 A) (@lem3212059 A s t)). Qed.
Lemma lem3212062 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term53 A s t) = (term18 A s t).
Proof. exact (@lem16933 (term18 A s t)). Qed.
Lemma lem3212063 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term53 A s t) = (term52 A s t).
Proof. exact (TRANS (@lem3212062 A s t) (@lem3212061 A s t)). Qed.
Lemma lem3212069 {A : Type'} (s : A -> Prop) (x : A) : (term54 A s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem3212072 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term55 A t s x) = (term55 A t s x).
Proof. exact (eq_refl (term55 A t s x)). Qed.
Lemma lem3212074 {A : Type'} (t : A -> Prop) (x : A) : (term56 A t x) = (term56 A t x).
Proof. exact (eq_refl (term56 A t x)). Qed.
Lemma lem3212075 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term57 A t s x) = (term58 A t s x).
Proof. exact (MK_COMB (@lem3212074 A t x) (@lem3212069 A s x)). Qed.
Lemma lem3212076 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3212077 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term59 A t s x) = (term60 A t s x).
Proof. exact (MK_COMB (@lem3212076) (@lem3212075 A t s x)). Qed.
Lemma lem3212078 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term61 A t s x) = (term62 A t s x).
Proof. exact (MK_COMB (@lem3212077 A t s x) (@lem3212072 A t s x)). Qed.
Lemma lem3212079 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term63 A t s x) = (term61 A t s x).
Proof. exact (@lem17646 (t x) (term22 A s x)). Qed.
Lemma lem3212080 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term63 A t s x) = (term62 A t s x).
Proof. exact (TRANS (@lem3212079 A t s x) (@lem3212078 A t s x)). Qed.
Lemma lem3212082 {A : Type'} (t : A -> Prop) (x : A) : (term64 A t x) = (term64 A t x).
Proof. exact (eq_refl (term64 A t x)). Qed.
Lemma lem3212083 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term65 A t s x) = (term66 A t s x).
Proof. exact (MK_COMB (@lem3212082 A t x) (@lem3212069 A s x)). Qed.
Lemma lem3212088 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term67 A t s x) = (term67 A t s x).
Proof. exact (eq_refl (term67 A t s x)). Qed.
Lemma lem3212089 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term68 A t s x) = (term69 A t s x).
Proof. exact (MK_COMB (@lem3212088 A t s x) (@lem3212083 A t s x)). Qed.
Lemma lem3212090 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : ((t x) = (term22 A s x)) = (term68 A t s x).
Proof. exact (@lem17500 (t x) (term22 A s x)). Qed.
Lemma lem3212091 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : ((t x) = (term22 A s x)) = (term69 A t s x).
Proof. exact (TRANS (@lem3212090 A t s x) (@lem3212089 A t s x)). Qed.
Lemma lem3212092 {A : Type'} (P : A -> Prop) : (term70 A P) = (term71 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3212093 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term72 A t s) = (term73 A t s).
Proof. exact (@lem3212092 A (term24 A t s)). Qed.
Lemma lem3212094 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term74 A t s x) = ((t x) = (term22 A s x)).
Proof. exact (eq_refl (term74 A t s x)). Qed.
Lemma lem3212095 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3212096 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term75 A t s x) = (term63 A t s x).
Proof. exact (MK_COMB (@lem3212095) (@lem3212094 A t s x)). Qed.
Lemma lem3212097 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term75 A t s x) = (term62 A t s x).
Proof. exact (TRANS (@lem3212096 A t s x) (@lem3212080 A t s x)). Qed.
Lemma lem3212098 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term76 A t s) = (term77 A t s).
Proof. exact (fun_ext (fun x : A => @lem3212097 A t s x)). Qed.
Lemma lem3212099 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3212100 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term73 A t s) = (term78 A t s).
Proof. exact (MK_COMB (@lem3212099 A) (@lem3212098 A t s)). Qed.
Lemma lem3212101 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term72 A t s) = (term78 A t s).
Proof. exact (TRANS (@lem3212093 A t s) (@lem3212100 A t s)). Qed.
Lemma lem3212102 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term24 A t s) = (term79 A t s).
Proof. exact (fun_ext (fun x : A => @lem3212091 A t s x)). Qed.
Lemma lem3212103 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3212104 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term25 A t s) = (term80 A t s).
Proof. exact (MK_COMB (@lem3212103 A) (@lem3212102 A t s)). Qed.
Lemma lem3212105 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3212106 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term81 A s t) = (term82 A s t).
Proof. exact (MK_COMB (@lem3212105) (@lem3212063 A s t)). Qed.
Lemma lem3212107 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term83 A t s) = (term84 A t s).
Proof. exact (MK_COMB (@lem3212106 A s t) (@lem3212104 A t s)). Qed.
Lemma lem3212108 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3212109 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term85 A s t) = (term86 A s t).
Proof. exact (MK_COMB (@lem3212108) (@lem3212058 A s t)). Qed.
Lemma lem3212110 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term87 A t s) = (term88 A t s).
Proof. exact (MK_COMB (@lem3212109 A s t) (@lem3212101 A t s)). Qed.
Lemma lem3212111 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3212112 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term89 A t s) = (term90 A t s).
Proof. exact (MK_COMB (@lem3212111) (@lem3212110 A t s)). Qed.
Lemma lem3212113 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term91 A t s) = (term92 A t s).
Proof. exact (MK_COMB (@lem3212112 A t s) (@lem3212107 A t s)). Qed.
Lemma lem3212114 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term39 A t s) = (term91 A t s).
Proof. exact (@lem17646 (term19 A s t) (term25 A t s)). Qed.
Lemma lem3212115 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term39 A t s) = (term92 A t s).
Proof. exact (TRANS (@lem3212114 A t s) (@lem3212113 A t s)). Qed.
Lemma lem3212213 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term93 A P Q) = (term94 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3212214 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term93 A P Q) = (term94 A P Q).
Proof. exact (@lem3212213 A P Q). Qed.
Lemma lem3212215 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term95 A s t) = (term96 A s t).
Proof. exact (@lem3212214 A (term97 A s t) (term98 A s t)). Qed.
Lemma lem3212216 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term99 A s t x) = (term100 A s t x).
Proof. exact (eq_refl (term99 A s t x)). Qed.
Lemma lem3212217 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3212218 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term101 A s t x) = (term102 A s t x).
Proof. exact (MK_COMB (@lem3212217) (@lem3212216 A s t x)). Qed.
Lemma lem3212219 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term103 A s t x) = (term104 A s t x).
Proof. exact (eq_refl (term103 A s t x)). Qed.
Lemma lem3212220 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term105 A s t x) = (term42 A s t x).
Proof. exact (MK_COMB (@lem3212218 A s t x) (@lem3212219 A s t x)). Qed.
Lemma lem3212221 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term106 A s t) = (term51 A s t).
Proof. exact (fun_ext (fun x : A => @lem3212220 A s t x)). Qed.
Lemma lem3212222 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3212223 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term95 A s t) = (term52 A s t).
Proof. exact (MK_COMB (@lem3212222 A) (@lem3212221 A s t)). Qed.
Lemma lem3212224 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3212225 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term107 A s t) = (term108 A s t).
Proof. exact (MK_COMB (@lem3212224) (@lem3212223 A s t)). Qed.
Lemma lem3212226 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term99 A s t x) = (term100 A s t x).
Proof. exact (eq_refl (term99 A s t x)). Qed.
Lemma lem3212227 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term109 A s t) = (term97 A s t).
Proof. exact (fun_ext (fun x : A => @lem3212226 A s t x)). Qed.
Lemma lem3212228 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3212229 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term110 A s t) = (term111 A s t).
Proof. exact (MK_COMB (@lem3212228 A) (@lem3212227 A s t)). Qed.
Lemma lem3212230 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3212231 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term112 A s t) = (term113 A s t).
Proof. exact (MK_COMB (@lem3212230) (@lem3212229 A s t)). Qed.
Lemma lem3212232 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term103 A s t x) = (term104 A s t x).
Proof. exact (eq_refl (term103 A s t x)). Qed.
Lemma lem3212233 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term114 A s t) = (term98 A s t).
Proof. exact (fun_ext (fun x : A => @lem3212232 A s t x)). Qed.
Lemma lem3212234 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3212235 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term115 A s t) = (term116 A s t).
Proof. exact (MK_COMB (@lem3212234 A) (@lem3212233 A s t)). Qed.
Lemma lem3212236 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term96 A s t) = (term117 A s t).
Proof. exact (MK_COMB (@lem3212231 A s t) (@lem3212235 A s t)). Qed.
Lemma lem3212237 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term95 A s t) = (term96 A s t)) = ((term52 A s t) = (term117 A s t)).
Proof. exact (MK_COMB (@lem3212225 A s t) (@lem3212236 A s t)). Qed.
Lemma lem3212238 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term52 A s t) = (term117 A s t).
Proof. exact (EQ_MP (@lem3212237 A s t) (@lem3212215 A s t)). Qed.
Lemma lem3212299 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3212300 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term82 A s t) = (term118 A s t).
Proof. exact (MK_COMB (@lem3212299) (@lem3212238 A s t)). Qed.
Lemma lem3212302 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term119 A P Q) = (term120 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3212303 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term119 A P Q) = (term120 A P Q).
Proof. exact (@lem3212302 A P Q). Qed.
Lemma lem3212304 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term121 A t s) = (term122 A t s).
Proof. exact (@lem3212303 A (term123 A t s) (term124 A t s)). Qed.
Lemma lem3212305 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term125 A t s x) = (term126 A t s x).
Proof. exact (eq_refl (term125 A t s x)). Qed.
Lemma lem3212306 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3212307 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term127 A t s x) = (term67 A t s x).
Proof. exact (MK_COMB (@lem3212306) (@lem3212305 A t s x)). Qed.
Lemma lem3212308 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term128 A t s x) = (term66 A t s x).
Proof. exact (eq_refl (term128 A t s x)). Qed.
Lemma lem3212309 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term129 A t s x) = (term69 A t s x).
Proof. exact (MK_COMB (@lem3212307 A t s x) (@lem3212308 A t s x)). Qed.
Lemma lem3212310 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term130 A t s) = (term79 A t s).
Proof. exact (fun_ext (fun x : A => @lem3212309 A t s x)). Qed.
Lemma lem3212311 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3212312 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term121 A t s) = (term80 A t s).
Proof. exact (MK_COMB (@lem3212311 A) (@lem3212310 A t s)). Qed.
Lemma lem3212313 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3212314 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term131 A t s) = (term132 A t s).
Proof. exact (MK_COMB (@lem3212313) (@lem3212312 A t s)). Qed.
Lemma lem3212315 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term125 A t s x) = (term126 A t s x).
Proof. exact (eq_refl (term125 A t s x)). Qed.
Lemma lem3212316 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term133 A t s) = (term123 A t s).
Proof. exact (fun_ext (fun x : A => @lem3212315 A t s x)). Qed.
Lemma lem3212317 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3212318 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term134 A t s) = (term135 A t s).
Proof. exact (MK_COMB (@lem3212317 A) (@lem3212316 A t s)). Qed.
Lemma lem3212319 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3212320 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term136 A t s) = (term137 A t s).
Proof. exact (MK_COMB (@lem3212319) (@lem3212318 A t s)). Qed.
Lemma lem3212321 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term128 A t s x) = (term66 A t s x).
Proof. exact (eq_refl (term128 A t s x)). Qed.
Lemma lem3212322 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term138 A t s) = (term124 A t s).
Proof. exact (fun_ext (fun x : A => @lem3212321 A t s x)). Qed.
Lemma lem3212323 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3212324 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term139 A t s) = (term140 A t s).
Proof. exact (MK_COMB (@lem3212323 A) (@lem3212322 A t s)). Qed.
Lemma lem3212325 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term122 A t s) = (term141 A t s).
Proof. exact (MK_COMB (@lem3212320 A t s) (@lem3212324 A t s)). Qed.
Lemma lem3212326 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term121 A t s) = (term122 A t s)) = ((term80 A t s) = (term141 A t s)).
Proof. exact (MK_COMB (@lem3212314 A t s) (@lem3212325 A t s)). Qed.
Lemma lem3212327 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term80 A t s) = (term141 A t s).
Proof. exact (EQ_MP (@lem3212326 A t s) (@lem3212304 A t s)). Qed.
Lemma lem3212388 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term84 A t s) = (term142 A t s).
Proof. exact (MK_COMB (@lem3212300 A s t) (@lem3212327 A t s)). Qed.
Lemma lem3212389 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term90 A t s) = (term90 A t s).
Proof. exact (eq_refl (term90 A t s)). Qed.
Lemma lem3212390 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term92 A t s) = (term143 A t s).
Proof. exact (MK_COMB (@lem3212389 A t s) (@lem3212388 A t s)). Qed.
Lemma lem3212392 {A : Type'} (P : A -> Prop) (Q : Prop) : (term144 A P Q) = (term145 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3212393 {A : Type'} (P : A -> Prop) (Q : Prop) : (term144 A P Q) = (term145 A P Q).
Proof. exact (@lem3212392 A P Q). Qed.
Lemma lem3212394 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term146 A t s) = (term147 A t s).
Proof. exact (@lem3212393 A (term49 A s t) (term78 A t s)). Qed.
Lemma lem3212395 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term148 A s t x) = (term41 A s t x).
Proof. exact (eq_refl (term148 A s t x)). Qed.
Lemma lem3212396 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term149 A s t) = (term49 A s t).
Proof. exact (fun_ext (fun x : A => @lem3212395 A s t x)). Qed.
Lemma lem3212397 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3212398 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term150 A s t) = (term50 A s t).
Proof. exact (MK_COMB (@lem3212397 A) (@lem3212396 A s t)). Qed.
Lemma lem3212399 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3212400 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term151 A s t) = (term86 A s t).
Proof. exact (MK_COMB (@lem3212399) (@lem3212398 A s t)). Qed.
Lemma lem3212401 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term78 A t s) = (term78 A t s).
Proof. exact (eq_refl (term78 A t s)). Qed.
Lemma lem3212402 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term146 A t s) = (term88 A t s).
Proof. exact (MK_COMB (@lem3212400 A s t) (@lem3212401 A t s)). Qed.
Lemma lem3212403 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3212404 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term152 A t s) = (term153 A t s).
Proof. exact (MK_COMB (@lem3212403) (@lem3212402 A t s)). Qed.
Lemma lem3212405 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term148 A s t x) = (term41 A s t x).
Proof. exact (eq_refl (term148 A s t x)). Qed.
Lemma lem3212406 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3212407 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term154 A s t x) = (term155 A s t x).
Proof. exact (MK_COMB (@lem3212406) (@lem3212405 A s t x)). Qed.
Lemma lem3212408 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term78 A t s) = (term78 A t s).
Proof. exact (eq_refl (term78 A t s)). Qed.
Lemma lem3212409 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term156 A x t s) = (term157 A x t s).
Proof. exact (MK_COMB (@lem3212407 A s t x) (@lem3212408 A t s)). Qed.
Lemma lem3212410 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term158 A t s) = (term159 A t s).
Proof. exact (fun_ext (fun x : A => @lem3212409 A x t s)). Qed.
Lemma lem3212411 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3212412 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term147 A t s) = (term160 A t s).
Proof. exact (MK_COMB (@lem3212411 A) (@lem3212410 A t s)). Qed.
Lemma lem3212413 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term146 A t s) = (term147 A t s)) = ((term88 A t s) = (term160 A t s)).
Proof. exact (MK_COMB (@lem3212404 A t s) (@lem3212412 A t s)). Qed.
Lemma lem3212414 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term88 A t s) = (term160 A t s).
Proof. exact (EQ_MP (@lem3212413 A t s) (@lem3212394 A t s)). Qed.
Lemma lem3212415 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3212416 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term90 A t s) = (term161 A t s).
Proof. exact (MK_COMB (@lem3212415) (@lem3212414 A t s)). Qed.
Lemma lem3212418 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term120 A P Q) = (term119 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3212419 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term120 A P Q) = (term119 A P Q).
Proof. exact (@lem3212418 A P Q). Qed.
Lemma lem3212420 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term122 A t s) = (term121 A t s).
Proof. exact (@lem3212419 A (term123 A t s) (term124 A t s)). Qed.
Lemma lem3212421 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term125 A t s x) = (term126 A t s x).
Proof. exact (eq_refl (term125 A t s x)). Qed.
Lemma lem3212422 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term133 A t s) = (term123 A t s).
Proof. exact (fun_ext (fun x : A => @lem3212421 A t s x)). Qed.
Lemma lem3212423 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3212424 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term134 A t s) = (term135 A t s).
Proof. exact (MK_COMB (@lem3212423 A) (@lem3212422 A t s)). Qed.
Lemma lem3212425 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3212426 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term136 A t s) = (term137 A t s).
Proof. exact (MK_COMB (@lem3212425) (@lem3212424 A t s)). Qed.
Lemma lem3212427 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term128 A t s x) = (term66 A t s x).
Proof. exact (eq_refl (term128 A t s x)). Qed.
Lemma lem3212428 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term138 A t s) = (term124 A t s).
Proof. exact (fun_ext (fun x : A => @lem3212427 A t s x)). Qed.
Lemma lem3212429 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3212430 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term139 A t s) = (term140 A t s).
Proof. exact (MK_COMB (@lem3212429 A) (@lem3212428 A t s)). Qed.
Lemma lem3212431 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term122 A t s) = (term141 A t s).
Proof. exact (MK_COMB (@lem3212426 A t s) (@lem3212430 A t s)). Qed.
Lemma lem3212432 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3212433 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term162 A t s) = (term163 A t s).
Proof. exact (MK_COMB (@lem3212432) (@lem3212431 A t s)). Qed.
Lemma lem3212434 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term125 A t s x) = (term126 A t s x).
Proof. exact (eq_refl (term125 A t s x)). Qed.
Lemma lem3212435 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3212436 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term127 A t s x) = (term67 A t s x).
Proof. exact (MK_COMB (@lem3212435) (@lem3212434 A t s x)). Qed.
Lemma lem3212437 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term128 A t s x) = (term66 A t s x).
Proof. exact (eq_refl (term128 A t s x)). Qed.
Lemma lem3212438 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term129 A t s x) = (term69 A t s x).
Proof. exact (MK_COMB (@lem3212436 A t s x) (@lem3212437 A t s x)). Qed.
Lemma lem3212439 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term130 A t s) = (term79 A t s).
Proof. exact (fun_ext (fun x : A => @lem3212438 A t s x)). Qed.
Lemma lem3212440 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3212441 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term121 A t s) = (term80 A t s).
Proof. exact (MK_COMB (@lem3212440 A) (@lem3212439 A t s)). Qed.
Lemma lem3212442 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term122 A t s) = (term121 A t s)) = ((term141 A t s) = (term80 A t s)).
Proof. exact (MK_COMB (@lem3212433 A t s) (@lem3212441 A t s)). Qed.
Lemma lem3212443 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term141 A t s) = (term80 A t s).
Proof. exact (EQ_MP (@lem3212442 A t s) (@lem3212420 A t s)). Qed.
Lemma lem3212444 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term118 A s t) = (term118 A s t).
Proof. exact (eq_refl (term118 A s t)). Qed.
Lemma lem3212445 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term142 A t s) = (term164 A t s).
Proof. exact (MK_COMB (@lem3212444 A s t) (@lem3212443 A t s)). Qed.
Lemma lem3212447 {A : Type'} (P : Prop) (Q : A -> Prop) : (term165 A P Q) = (term166 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3212448 {A : Type'} (P : Prop) (Q : A -> Prop) : (term165 A P Q) = (term166 A P Q).
Proof. exact (@lem3212447 A P Q). Qed.
Lemma lem3212449 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term167 A t s) = (term168 A t s).
Proof. exact (@lem3212448 A (term117 A s t) (term79 A t s)). Qed.
Lemma lem3212450 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term169 A t s x) = (term69 A t s x).
Proof. exact (eq_refl (term169 A t s x)). Qed.
Lemma lem3212451 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term170 A t s) = (term79 A t s).
Proof. exact (fun_ext (fun x : A => @lem3212450 A t s x)). Qed.
Lemma lem3212452 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3212453 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term171 A t s) = (term80 A t s).
Proof. exact (MK_COMB (@lem3212452 A) (@lem3212451 A t s)). Qed.
Lemma lem3212454 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term118 A s t) = (term118 A s t).
Proof. exact (eq_refl (term118 A s t)). Qed.
Lemma lem3212455 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term167 A t s) = (term164 A t s).
Proof. exact (MK_COMB (@lem3212454 A s t) (@lem3212453 A t s)). Qed.
Lemma lem3212456 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3212457 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term172 A t s) = (term173 A t s).
Proof. exact (MK_COMB (@lem3212456) (@lem3212455 A t s)). Qed.
Lemma lem3212458 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term169 A t s x) = (term69 A t s x).
Proof. exact (eq_refl (term169 A t s x)). Qed.
Lemma lem3212459 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term118 A s t) = (term118 A s t).
Proof. exact (eq_refl (term118 A s t)). Qed.
Lemma lem3212460 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term174 A t s x) = (term175 A t s x).
Proof. exact (MK_COMB (@lem3212459 A s t) (@lem3212458 A t s x)). Qed.
Lemma lem3212461 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term176 A t s) = (term177 A t s).
Proof. exact (fun_ext (fun x : A => @lem3212460 A t s x)). Qed.
Lemma lem3212462 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3212463 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term168 A t s) = (term178 A t s).
Proof. exact (MK_COMB (@lem3212462 A) (@lem3212461 A t s)). Qed.
Lemma lem3212464 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term167 A t s) = (term168 A t s)) = ((term164 A t s) = (term178 A t s)).
Proof. exact (MK_COMB (@lem3212457 A t s) (@lem3212463 A t s)). Qed.
Lemma lem3212465 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term164 A t s) = (term178 A t s).
Proof. exact (EQ_MP (@lem3212464 A t s) (@lem3212449 A t s)). Qed.
Lemma lem3212466 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term142 A t s) = (term178 A t s).
Proof. exact (TRANS (@lem3212445 A t s) (@lem3212465 A t s)). Qed.
Lemma lem3212467 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term143 A t s) = (term179 A t s).
Proof. exact (MK_COMB (@lem3212416 A t s) (@lem3212466 A t s)). Qed.
Lemma lem3212469 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term120 A P Q) = (term119 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3212470 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term120 A P Q) = (term119 A P Q).
Proof. exact (@lem3212469 A P Q). Qed.
Lemma lem3212471 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term180 A t s) = (term181 A t s).
Proof. exact (@lem3212470 A (term159 A t s) (term177 A t s)). Qed.
Lemma lem3212472 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term182 A t s x) = (term157 A x t s).
Proof. exact (eq_refl (term182 A t s x)). Qed.
Lemma lem3212473 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term183 A t s) = (term159 A t s).
Proof. exact (fun_ext (fun x : A => @lem3212472 A x t s)). Qed.
Lemma lem3212474 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3212475 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term184 A t s) = (term160 A t s).
Proof. exact (MK_COMB (@lem3212474 A) (@lem3212473 A t s)). Qed.
Lemma lem3212476 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3212477 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term185 A t s) = (term161 A t s).
Proof. exact (MK_COMB (@lem3212476) (@lem3212475 A t s)). Qed.
Lemma lem3212478 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term186 A t s x) = (term175 A t s x).
Proof. exact (eq_refl (term186 A t s x)). Qed.
Lemma lem3212479 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term187 A t s) = (term177 A t s).
Proof. exact (fun_ext (fun x : A => @lem3212478 A t s x)). Qed.
Lemma lem3212480 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3212481 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term188 A t s) = (term178 A t s).
Proof. exact (MK_COMB (@lem3212480 A) (@lem3212479 A t s)). Qed.
Lemma lem3212482 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term180 A t s) = (term179 A t s).
Proof. exact (MK_COMB (@lem3212477 A t s) (@lem3212481 A t s)). Qed.
Lemma lem3212483 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3212484 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term189 A t s) = (term190 A t s).
Proof. exact (MK_COMB (@lem3212483) (@lem3212482 A t s)). Qed.
Lemma lem3212485 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term182 A t s x) = (term157 A x t s).
Proof. exact (eq_refl (term182 A t s x)). Qed.
Lemma lem3212486 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3212487 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term191 A t s x) = (term192 A x t s).
Proof. exact (MK_COMB (@lem3212486) (@lem3212485 A x t s)). Qed.
Lemma lem3212488 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term186 A t s x) = (term175 A t s x).
Proof. exact (eq_refl (term186 A t s x)). Qed.
Lemma lem3212489 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term193 A t s x) = (term194 A t s x).
Proof. exact (MK_COMB (@lem3212487 A x t s) (@lem3212488 A t s x)). Qed.
Lemma lem3212490 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term195 A t s) = (term196 A t s).
Proof. exact (fun_ext (fun x : A => @lem3212489 A t s x)). Qed.
Lemma lem3212491 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3212492 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term181 A t s) = (term197 A t s).
Proof. exact (MK_COMB (@lem3212491 A) (@lem3212490 A t s)). Qed.
Lemma lem3212493 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term180 A t s) = (term181 A t s)) = ((term179 A t s) = (term197 A t s)).
Proof. exact (MK_COMB (@lem3212484 A t s) (@lem3212492 A t s)). Qed.
Lemma lem3212494 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term179 A t s) = (term197 A t s).
Proof. exact (EQ_MP (@lem3212493 A t s) (@lem3212471 A t s)). Qed.
Lemma lem3212495 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term143 A t s) = (term197 A t s).
Proof. exact (TRANS (@lem3212467 A t s) (@lem3212494 A t s)). Qed.
Lemma lem3212496 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term92 A t s) = (term197 A t s).
Proof. exact (TRANS (@lem3212390 A t s) (@lem3212495 A t s)). Qed.
Lemma lem3212497 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term39 A t s) = (term197 A t s).
Proof. exact (TRANS (@lem3212115 A t s) (@lem3212496 A t s)). Qed.
Lemma lem3212498 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term39 A t s) : term197 A t s.
Proof. exact (EQ_MP (@lem3212497 A t s) (@lem3212022 A t s h1)). Qed.
Lemma lem3212499 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term194 A t s x) : term194 A t s x.
Proof. exact (h1). Qed.
Lemma lem3212524 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term69 A t s x) = (term69 A t s x).
Proof. exact (eq_refl (term69 A t s x)). Qed.
Lemma lem3212535 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term104 A s t x) = (term104 A s t x).
Proof. exact (eq_refl (term104 A s t x)). Qed.
Lemma lem3212536 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term98 A s t) = (term98 A s t).
Proof. exact (fun_ext (fun x : A => @lem3212535 A s t x)). Qed.
Lemma lem3212537 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3212538 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term116 A s t) = (term116 A s t).
Proof. exact (MK_COMB (@lem3212537 A) (@lem3212536 A s t)). Qed.
Lemma lem3212549 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term100 A s t x) = (term100 A s t x).
Proof. exact (eq_refl (term100 A s t x)). Qed.
Lemma lem3212550 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term97 A s t) = (term97 A s t).
Proof. exact (fun_ext (fun x : A => @lem3212549 A s t x)). Qed.
Lemma lem3212551 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3212552 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term111 A s t) = (term111 A s t).
Proof. exact (MK_COMB (@lem3212551 A) (@lem3212550 A s t)). Qed.
Lemma lem3212553 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3212554 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term113 A s t) = (term113 A s t).
Proof. exact (MK_COMB (@lem3212553) (@lem3212552 A s t)). Qed.
Lemma lem3212555 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term117 A s t) = (term117 A s t).
Proof. exact (MK_COMB (@lem3212554 A s t) (@lem3212538 A s t)). Qed.
Lemma lem3212556 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3212557 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term118 A s t) = (term118 A s t).
Proof. exact (MK_COMB (@lem3212556) (@lem3212555 A s t)). Qed.
Lemma lem3212558 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term175 A t s x) = (term175 A t s x).
Proof. exact (MK_COMB (@lem3212557 A s t) (@lem3212524 A t s x)). Qed.
Lemma lem3212583 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term62 A t s x) = (term62 A t s x).
Proof. exact (eq_refl (term62 A t s x)). Qed.
Lemma lem3212584 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term77 A t s) = (term77 A t s).
Proof. exact (fun_ext (fun x : A => @lem3212583 A t s x)). Qed.
Lemma lem3212585 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3212586 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term78 A t s) = (term78 A t s).
Proof. exact (MK_COMB (@lem3212585 A) (@lem3212584 A t s)). Qed.
Lemma lem3212613 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term155 A s t x) = (term155 A s t x).
Proof. exact (eq_refl (term155 A s t x)). Qed.
Lemma lem3212614 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term157 A x t s) = (term157 A x t s).
Proof. exact (MK_COMB (@lem3212613 A s t x) (@lem3212586 A t s)). Qed.
Lemma lem3212615 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3212616 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term192 A x t s) = (term192 A x t s).
Proof. exact (MK_COMB (@lem3212615) (@lem3212614 A x t s)). Qed.
Lemma lem3212617 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term194 A t s x) = (term194 A t s x).
Proof. exact (MK_COMB (@lem3212616 A x t s) (@lem3212558 A t s x)). Qed.
Lemma lem3212618 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term194 A t s x) : term194 A t s x.
Proof. exact (EQ_MP (@lem3212617 A t s x) (@lem3212499 A t s x h1)). Qed.
Lemma lem3212619 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term157 A x t s) : term157 A x t s.
Proof. exact (h1). Qed.
Lemma lem3212620 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term175 A t s x) : term175 A t s x.
Proof. exact (h1). Qed.
Lemma lem3212621 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term157 A x t s) : term78 A t s.
Proof. exact (proj2 (@lem3212619 A x t s h1)). Qed.
Lemma lem3212622 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term157 A x t s) : term41 A s t x.
Proof. exact (proj1 (@lem3212619 A x t s h1)). Qed.
Lemma lem3212623 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term157 A x t s) : term198 A s t x.
Proof. exact (proj2 (@lem3212622 A x t s h1)). Qed.
Lemma lem3212624 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term157 A x t s) : term199 A s t x.
Proof. exact (proj1 (@lem3212622 A x t s h1)). Qed.
Lemma lem3212631 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term175 A t s x) : term69 A t s x.
Proof. exact (proj2 (@lem3212620 A t s x h1)). Qed.
Lemma lem3212632 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term175 A t s x) : term117 A s t.
Proof. exact (proj1 (@lem3212620 A t s x h1)). Qed.
Lemma lem3212633 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term175 A t s x) : term116 A s t.
Proof. exact (proj2 (@lem3212632 A t s x h1)). Qed.
Lemma lem3212634 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term175 A t s x) : term111 A s t.
Proof. exact (proj1 (@lem3212632 A t s x h1)). Qed.
Lemma lem3212635 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term126 A t s x) : term126 A t s x.
Proof. exact (h1). Qed.
Lemma lem3212636 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term66 A t s x) : term66 A t s x.
Proof. exact (h1). Qed.
Lemma lem3212683 {A : Type'} (s : A -> Prop) (x : A) (h1 : term22 A s x) : term22 A s x.
Proof. exact (h1). Qed.
Lemma lem3212687 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3212702 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term62 A t s x) = (term200 A t s x).
Proof. exact (@lem19490 (term22 A t x) (term58 A t s x) (term22 A s x)). Qed.
Lemma lem3212709 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term201 A t s x) = (term202 A t s x).
Proof. exact (@lem19699 (t x) (s x) (term22 A s x)). Qed.
Lemma lem3212716 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term203 A s t x) = (term204 A s t x).
Proof. exact (@lem19699 (t x) (s x) (term22 A t x)). Qed.
Lemma lem3212717 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3212718 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term205 A s t x) = (term206 A s t x).
Proof. exact (MK_COMB (@lem3212717) (@lem3212716 A s t x)). Qed.
Lemma lem3212719 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term200 A t s x) = (term207 A t s x).
Proof. exact (MK_COMB (@lem3212718 A s t x) (@lem3212709 A t s x)). Qed.
Lemma lem3212721 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term62 A t s x) = (term207 A t s x).
Proof. exact (TRANS (@lem3212702 A t s x) (@lem3212719 A t s x)). Qed.
Lemma lem3212722 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term77 A t s) = (term208 A t s).
Proof. exact (fun_ext (fun x : A => @lem3212721 A t s x)). Qed.
Lemma lem3212723 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3212725 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term78 A t s) = (term209 A t s).
Proof. exact (MK_COMB (@lem3212723 A) (@lem3212722 A t s)). Qed.
Lemma lem3212726 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term157 A x t s) : term209 A t s.
Proof. exact (EQ_MP (@lem3212725 A t s) (@lem3212621 A x t s h1)). Qed.
Lemma lem3212730 {A : Type'} (s : A -> Prop) (x : A) (h1 : term22 A s x) : term22 A s x.
Proof. exact (h1). Qed.
Lemma lem3212734 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3212749 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term62 A t s x) = (term200 A t s x).
Proof. exact (@lem19490 (term22 A t x) (term58 A t s x) (term22 A s x)). Qed.
Lemma lem3212756 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term201 A t s x) = (term202 A t s x).
Proof. exact (@lem19699 (t x) (s x) (term22 A s x)). Qed.
Lemma lem3212763 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term203 A s t x) = (term204 A s t x).
Proof. exact (@lem19699 (t x) (s x) (term22 A t x)). Qed.
Lemma lem3212764 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3212765 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term205 A s t x) = (term206 A s t x).
Proof. exact (MK_COMB (@lem3212764) (@lem3212763 A s t x)). Qed.
Lemma lem3212766 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term200 A t s x) = (term207 A t s x).
Proof. exact (MK_COMB (@lem3212765 A s t x) (@lem3212756 A t s x)). Qed.
Lemma lem3212768 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term62 A t s x) = (term207 A t s x).
Proof. exact (TRANS (@lem3212749 A t s x) (@lem3212766 A t s x)). Qed.
Lemma lem3212769 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term77 A t s) = (term208 A t s).
Proof. exact (fun_ext (fun x : A => @lem3212768 A t s x)). Qed.
Lemma lem3212770 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3212772 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term78 A t s) = (term209 A t s).
Proof. exact (MK_COMB (@lem3212770 A) (@lem3212769 A t s)). Qed.
Lemma lem3212773 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term157 A x t s) : term209 A t s.
Proof. exact (EQ_MP (@lem3212772 A t s) (@lem3212621 A x t s h1)). Qed.
Lemma lem3212777 {A : Type'} (t : A -> Prop) (x : A) (h1 : term22 A t x) : term22 A t x.
Proof. exact (h1). Qed.
Lemma lem3212781 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3212824 {A : Type'} (t : A -> Prop) (x : A) (h1 : term22 A t x) : term22 A t x.
Proof. exact (h1). Qed.
Lemma lem3212828 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3212836 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term100 A s t x) = (term100 A s t x).
Proof. exact (eq_refl (term100 A s t x)). Qed.
Lemma lem3212837 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term97 A s t) = (term97 A s t).
Proof. exact (fun_ext (fun x : A => @lem3212836 A s t x)). Qed.
Lemma lem3212838 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3212840 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term111 A s t) = (term111 A s t).
Proof. exact (MK_COMB (@lem3212838 A) (@lem3212837 A s t)). Qed.
Lemma lem3212841 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term175 A t s x) : term111 A s t.
Proof. exact (EQ_MP (@lem3212840 A s t) (@lem3212634 A t s x h1)). Qed.
Lemma lem3212883 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term104 A s t x) = (term104 A s t x).
Proof. exact (eq_refl (term104 A s t x)). Qed.
Lemma lem3212884 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term98 A s t) = (term98 A s t).
Proof. exact (fun_ext (fun x : A => @lem3212883 A s t x)). Qed.
Lemma lem3212885 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3212887 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term116 A s t) = (term116 A s t).
Proof. exact (MK_COMB (@lem3212885 A) (@lem3212884 A s t)). Qed.
Lemma lem3212888 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term175 A t s x) : term116 A s t.
Proof. exact (EQ_MP (@lem3212887 A s t) (@lem3212633 A t s x h1)). Qed.
Lemma lem3212900 {A : Type'} (_33009 : A) (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term157 A x t s) : term210 A t s _33009.
Proof. exact (@lem3212726 A x t s h1 _33009). Qed.
Lemma lem3212901 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33009 : A) : (term210 A t s _33009) = (term207 A t s _33009).
Proof. exact (eq_refl (term210 A t s _33009)). Qed.
Lemma lem3212902 {A : Type'} (_33009 : A) (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term157 A x t s) : term207 A t s _33009.
Proof. exact (EQ_MP (@lem3212901 A t s _33009) (@lem3212900 A _33009 x t s h1)). Qed.
Lemma lem3212903 {A : Type'} (_33010 : A) (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term157 A x t s) : term210 A t s _33010.
Proof. exact (@lem3212773 A x t s h1 _33010). Qed.
Lemma lem3212904 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33010 : A) : (term210 A t s _33010) = (term207 A t s _33010).
Proof. exact (eq_refl (term210 A t s _33010)). Qed.
Lemma lem3212905 {A : Type'} (_33010 : A) (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term157 A x t s) : term207 A t s _33010.
Proof. exact (EQ_MP (@lem3212904 A t s _33010) (@lem3212903 A _33010 x t s h1)). Qed.
Lemma lem3212909 {A : Type'} (_33012 : A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term175 A t s x) : term99 A s t _33012.
Proof. exact (@lem3212841 A t s x h1 _33012). Qed.
Lemma lem3212910 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33012 : A) : (term99 A s t _33012) = (term100 A s t _33012).
Proof. exact (eq_refl (term99 A s t _33012)). Qed.
Lemma lem3212918 {A : Type'} (_33015 : A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term175 A t s x) : term103 A s t _33015.
Proof. exact (@lem3212888 A t s x h1 _33015). Qed.
Lemma lem3212919 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33015 : A) : (term103 A s t _33015) = (term104 A s t _33015).
Proof. exact (eq_refl (term103 A s t _33015)). Qed.
Lemma lem3212928 {A : Type'} (_33009 : A) (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term157 A x t s) : term204 A s t _33009.
Proof. exact (proj1 (@lem3212902 A _33009 x t s h1)). Qed.
Lemma lem3212933 {A : Type'} (_33010 : A) (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term157 A x t s) : term202 A t s _33010.
Proof. exact (proj2 (@lem3212905 A _33010 x t s h1)). Qed.
Lemma lem3212946 {A : Type'} (s : A -> Prop) (x : A) (h1 : term22 A s x) : term22 A s x.
Proof. exact (h1). Qed.
Lemma lem3212948 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3212974 {A : Type'} (s : A -> Prop) (x : A) (h1 : term22 A s x) : term22 A s x.
Proof. exact (h1). Qed.
Lemma lem3212976 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3213000 {A : Type'} (_33009 : A) (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term157 A x t s) : term100 A s t _33009.
Proof. exact (proj2 (@lem3212928 A _33009 x t s h1)). Qed.
Lemma lem3213002 {A : Type'} (t : A -> Prop) (x : A) (h1 : term22 A t x) : term22 A t x.
Proof. exact (h1). Qed.
Lemma lem3213004 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3213010 {A : Type'} (_33010 : A) (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term157 A x t s) : term100 A t s _33010.
Proof. exact (proj1 (@lem3212933 A _33010 x t s h1)). Qed.
Lemma lem3213030 {A : Type'} (t : A -> Prop) (x : A) (h1 : term22 A t x) : term22 A t x.
Proof. exact (h1). Qed.
Lemma lem3213032 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3213062 {A : Type'} (_33012 : A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term175 A t s x) : term100 A s t _33012.
Proof. exact (EQ_MP (@lem3212910 A s t _33012) (@lem3212909 A _33012 t s x h1)). Qed.
Lemma lem3213072 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term126 A t s x) : term22 A s x.
Proof. exact (proj2 (@lem3212635 A t s x h1)). Qed.
Lemma lem3213084 {A : Type'} (_33015 : A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term175 A t s x) : term104 A s t _33015.
Proof. exact (EQ_MP (@lem3212919 A s t _33015) (@lem3212918 A _33015 t s x h1)). Qed.
Lemma lem3213086 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term66 A t s x) : term22 A t x.
Proof. exact (proj1 (@lem3212636 A t s x h1)). Qed.
Lemma lem3213090 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3213091 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term211 A s x.
Proof. exact (fun h0 : term22 A s x => @lem3213090 A s x h1). Qed.
Lemma lem3213093 (p : Prop) : (term212 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3213094 {A : Type'} (s : A -> Prop) (x : A) : (term211 A s x) = (s x).
Proof. exact (@lem3213093 (s x)). Qed.
Lemma lem3213095 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3213094 A s x) (@lem3213091 A s x h1)). Qed.
Lemma lem3213098 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3213100 {A : Type'} (s : A -> Prop) (x : A) : (term22 A s x) = (term213 A s x).
Proof. exact (@lem3213098 (s x)). Qed.
Lemma lem3213103 {A : Type'} (s : A -> Prop) (x : A) (h1 : term22 A s x) : term213 A s x.
Proof. exact (EQ_MP (@lem3213100 A s x) (@lem3212946 A s x h1)). Qed.
Lemma lem3213106 {A : Type'} (s : A -> Prop) (x : A) (h1 : term22 A s x) (h2 : s x) : False.
Proof. exact (@lem3213103 A s x h1 (@lem3213095 A s x h2)). Qed.
Lemma lem3213107 {A : Type'} (s : A -> Prop) (x : A) (h1 : term22 A s x) (h2 : s x) : term214.
Proof. exact (fun h0 : ~ False => @lem3213106 A s x h1 h2). Qed.
Lemma lem3213109 (p : Prop) : (term212 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3213110 : term214 = False.
Proof. exact (@lem3213109 False). Qed.
Lemma lem3213111 {A : Type'} (s : A -> Prop) (x : A) (h1 : term22 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3213110) (@lem3213107 A s x h1 h2)). Qed.
Lemma lem3213113 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3213114 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term211 A t x.
Proof. exact (fun h0 : term22 A t x => @lem3213113 A t x h1). Qed.
Lemma lem3213116 (p : Prop) : (term212 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3213117 {A : Type'} (t : A -> Prop) (x : A) : (term211 A t x) = (t x).
Proof. exact (@lem3213116 (t x)). Qed.
Lemma lem3213118 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3213117 A t x) (@lem3213114 A t x h1)). Qed.
Lemma lem3213120 (b : Prop) (a : Prop) : (a \/ b) = (term215 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3213121 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33009 : A) : (term100 A s t _33009) = (term216 A t s _33009).
Proof. exact (@lem3213120 (term22 A t _33009) (s _33009)). Qed.
Lemma lem3213123 (a : Prop) : (term37 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3213124 {A : Type'} (t : A -> Prop) (_33009 : A) : (term54 A t _33009) = (t _33009).
Proof. exact (@lem3213123 (t _33009)). Qed.
Lemma lem3213125 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3213126 {A : Type'} (t : A -> Prop) (_33009 : A) : (term217 A t _33009) = (term218 A t _33009).
Proof. exact (MK_COMB (@lem3213125) (@lem3213124 A t _33009)). Qed.
Lemma lem3213127 {A : Type'} (s : A -> Prop) (_33009 : A) : (s _33009) = (s _33009).
Proof. exact (eq_refl (s _33009)). Qed.
Lemma lem3213128 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33009 : A) : (term216 A t s _33009) = (term219 A t s _33009).
Proof. exact (MK_COMB (@lem3213126 A t _33009) (@lem3213127 A s _33009)). Qed.
Lemma lem3213129 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33009 : A) : (term100 A s t _33009) = (term219 A t s _33009).
Proof. exact (TRANS (@lem3213121 A t s _33009) (@lem3213128 A t s _33009)). Qed.
Lemma lem3213132 {A : Type'} (_33009 : A) (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term157 A x t s) : term219 A t s _33009.
Proof. exact (EQ_MP (@lem3213129 A t s _33009) (@lem3213000 A _33009 x t s h1)). Qed.
Lemma lem3213133 {A : Type'} (_33009 : A) (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term157 A x t s) : term219 A t s _33009.
Proof. exact (@lem3213132 A _33009 x t s h1). Qed.
Lemma lem3213134 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term157 A x t s) : term219 A t s x.
Proof. exact (@lem3213133 A x x t s h1). Qed.
Lemma lem3213137 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : t x) (h2 : term157 A x t s) : s x.
Proof. exact (@lem3213134 A x t s h2 (@lem3213118 A t x h1)). Qed.
Lemma lem3213138 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : t x) (h2 : term157 A x t s) : term211 A s x.
Proof. exact (fun h0 : term22 A s x => @lem3213137 A x t s h1 h2). Qed.
Lemma lem3213140 (p : Prop) : (term212 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3213141 {A : Type'} (s : A -> Prop) (x : A) : (term211 A s x) = (s x).
Proof. exact (@lem3213140 (s x)). Qed.
Lemma lem3213142 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : t x) (h2 : term157 A x t s) : s x.
Proof. exact (EQ_MP (@lem3213141 A s x) (@lem3213138 A x t s h1 h2)). Qed.
Lemma lem3213145 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3213147 {A : Type'} (s : A -> Prop) (x : A) : (term22 A s x) = (term213 A s x).
Proof. exact (@lem3213145 (s x)). Qed.
Lemma lem3213150 {A : Type'} (s : A -> Prop) (x : A) (h1 : term22 A s x) : term213 A s x.
Proof. exact (EQ_MP (@lem3213147 A s x) (@lem3212974 A s x h1)). Qed.
Lemma lem3213153 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A s x) (h2 : t x) (h3 : term157 A x t s) : False.
Proof. exact (@lem3213150 A s x h1 (@lem3213142 A x t s h2 h3)). Qed.
Lemma lem3213154 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A s x) (h2 : t x) (h3 : term157 A x t s) : term214.
Proof. exact (fun h0 : ~ False => @lem3213153 A x t s h1 h2 h3). Qed.
Lemma lem3213156 (p : Prop) : (term212 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3213157 : term214 = False.
Proof. exact (@lem3213156 False). Qed.
Lemma lem3213158 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A s x) (h2 : t x) (h3 : term157 A x t s) : False.
Proof. exact (EQ_MP (@lem3213157) (@lem3213154 A x t s h1 h2 h3)). Qed.
Lemma lem3213160 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3213161 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term211 A s x.
Proof. exact (fun h0 : term22 A s x => @lem3213160 A s x h1). Qed.
Lemma lem3213163 (p : Prop) : (term212 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3213164 {A : Type'} (s : A -> Prop) (x : A) : (term211 A s x) = (s x).
Proof. exact (@lem3213163 (s x)). Qed.
Lemma lem3213165 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3213164 A s x) (@lem3213161 A s x h1)). Qed.
Lemma lem3213167 (b : Prop) (a : Prop) : (a \/ b) = (term215 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3213168 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33010 : A) : (term100 A t s _33010) = (term216 A s t _33010).
Proof. exact (@lem3213167 (term22 A s _33010) (t _33010)). Qed.
Lemma lem3213170 (a : Prop) : (term37 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3213171 {A : Type'} (s : A -> Prop) (_33010 : A) : (term54 A s _33010) = (s _33010).
Proof. exact (@lem3213170 (s _33010)). Qed.
Lemma lem3213172 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3213173 {A : Type'} (s : A -> Prop) (_33010 : A) : (term217 A s _33010) = (term218 A s _33010).
Proof. exact (MK_COMB (@lem3213172) (@lem3213171 A s _33010)). Qed.
Lemma lem3213174 {A : Type'} (t : A -> Prop) (_33010 : A) : (t _33010) = (t _33010).
Proof. exact (eq_refl (t _33010)). Qed.
Lemma lem3213175 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33010 : A) : (term216 A s t _33010) = (term219 A s t _33010).
Proof. exact (MK_COMB (@lem3213173 A s _33010) (@lem3213174 A t _33010)). Qed.
Lemma lem3213176 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33010 : A) : (term100 A t s _33010) = (term219 A s t _33010).
Proof. exact (TRANS (@lem3213168 A s t _33010) (@lem3213175 A s t _33010)). Qed.
Lemma lem3213179 {A : Type'} (_33010 : A) (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term157 A x t s) : term219 A s t _33010.
Proof. exact (EQ_MP (@lem3213176 A s t _33010) (@lem3213010 A _33010 x t s h1)). Qed.
Lemma lem3213180 {A : Type'} (_33010 : A) (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term157 A x t s) : term219 A s t _33010.
Proof. exact (@lem3213179 A _33010 x t s h1). Qed.
Lemma lem3213181 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term157 A x t s) : term219 A s t x.
Proof. exact (@lem3213180 A x x t s h1). Qed.
Lemma lem3213184 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : s x) (h2 : term157 A x t s) : t x.
Proof. exact (@lem3213181 A x t s h2 (@lem3213165 A s x h1)). Qed.
Lemma lem3213185 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : s x) (h2 : term157 A x t s) : term211 A t x.
Proof. exact (fun h0 : term22 A t x => @lem3213184 A x t s h1 h2). Qed.
Lemma lem3213187 (p : Prop) : (term212 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3213188 {A : Type'} (t : A -> Prop) (x : A) : (term211 A t x) = (t x).
Proof. exact (@lem3213187 (t x)). Qed.
Lemma lem3213189 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : s x) (h2 : term157 A x t s) : t x.
Proof. exact (EQ_MP (@lem3213188 A t x) (@lem3213185 A x t s h1 h2)). Qed.
Lemma lem3213192 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3213194 {A : Type'} (t : A -> Prop) (x : A) : (term22 A t x) = (term213 A t x).
Proof. exact (@lem3213192 (t x)). Qed.
Lemma lem3213197 {A : Type'} (t : A -> Prop) (x : A) (h1 : term22 A t x) : term213 A t x.
Proof. exact (EQ_MP (@lem3213194 A t x) (@lem3213002 A t x h1)). Qed.
Lemma lem3213200 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A t x) (h2 : s x) (h3 : term157 A x t s) : False.
Proof. exact (@lem3213197 A t x h1 (@lem3213189 A x t s h2 h3)). Qed.
Lemma lem3213201 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A t x) (h2 : s x) (h3 : term157 A x t s) : term214.
Proof. exact (fun h0 : ~ False => @lem3213200 A x t s h1 h2 h3). Qed.
Lemma lem3213203 (p : Prop) : (term212 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3213204 : term214 = False.
Proof. exact (@lem3213203 False). Qed.
Lemma lem3213205 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A t x) (h2 : s x) (h3 : term157 A x t s) : False.
Proof. exact (EQ_MP (@lem3213204) (@lem3213201 A x t s h1 h2 h3)). Qed.
Lemma lem3213207 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3213208 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term211 A t x.
Proof. exact (fun h0 : term22 A t x => @lem3213207 A t x h1). Qed.
Lemma lem3213210 (p : Prop) : (term212 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3213211 {A : Type'} (t : A -> Prop) (x : A) : (term211 A t x) = (t x).
Proof. exact (@lem3213210 (t x)). Qed.
Lemma lem3213212 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3213211 A t x) (@lem3213208 A t x h1)). Qed.
Lemma lem3213215 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3213217 {A : Type'} (t : A -> Prop) (x : A) : (term22 A t x) = (term213 A t x).
Proof. exact (@lem3213215 (t x)). Qed.
Lemma lem3213220 {A : Type'} (t : A -> Prop) (x : A) (h1 : term22 A t x) : term213 A t x.
Proof. exact (EQ_MP (@lem3213217 A t x) (@lem3213030 A t x h1)). Qed.
Lemma lem3213223 {A : Type'} (t : A -> Prop) (x : A) (h1 : term22 A t x) (h2 : t x) : False.
Proof. exact (@lem3213220 A t x h1 (@lem3213212 A t x h2)). Qed.
Lemma lem3213224 {A : Type'} (t : A -> Prop) (x : A) (h1 : term22 A t x) (h2 : t x) : term214.
Proof. exact (fun h0 : ~ False => @lem3213223 A t x h1 h2). Qed.
Lemma lem3213226 (p : Prop) : (term212 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3213227 : term214 = False.
Proof. exact (@lem3213226 False). Qed.
Lemma lem3213228 {A : Type'} (t : A -> Prop) (x : A) (h1 : term22 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3213227) (@lem3213224 A t x h1 h2)). Qed.
Lemma lem3213230 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term126 A t s x) : t x.
Proof. exact (proj1 (@lem3212635 A t s x h1)). Qed.
Lemma lem3213231 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term126 A t s x) : term211 A t x.
Proof. exact (fun h0 : term22 A t x => @lem3213230 A t s x h1). Qed.
Lemma lem3213233 (p : Prop) : (term212 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3213234 {A : Type'} (t : A -> Prop) (x : A) : (term211 A t x) = (t x).
Proof. exact (@lem3213233 (t x)). Qed.
Lemma lem3213235 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term126 A t s x) : t x.
Proof. exact (EQ_MP (@lem3213234 A t x) (@lem3213231 A t s x h1)). Qed.
Lemma lem3213237 (b : Prop) (a : Prop) : (a \/ b) = (term215 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3213238 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33012 : A) : (term100 A s t _33012) = (term216 A t s _33012).
Proof. exact (@lem3213237 (term22 A t _33012) (s _33012)). Qed.
Lemma lem3213240 (a : Prop) : (term37 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3213241 {A : Type'} (t : A -> Prop) (_33012 : A) : (term54 A t _33012) = (t _33012).
Proof. exact (@lem3213240 (t _33012)). Qed.
Lemma lem3213242 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3213243 {A : Type'} (t : A -> Prop) (_33012 : A) : (term217 A t _33012) = (term218 A t _33012).
Proof. exact (MK_COMB (@lem3213242) (@lem3213241 A t _33012)). Qed.
Lemma lem3213244 {A : Type'} (s : A -> Prop) (_33012 : A) : (s _33012) = (s _33012).
Proof. exact (eq_refl (s _33012)). Qed.
Lemma lem3213245 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33012 : A) : (term216 A t s _33012) = (term219 A t s _33012).
Proof. exact (MK_COMB (@lem3213243 A t _33012) (@lem3213244 A s _33012)). Qed.
Lemma lem3213246 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33012 : A) : (term100 A s t _33012) = (term219 A t s _33012).
Proof. exact (TRANS (@lem3213238 A t s _33012) (@lem3213245 A t s _33012)). Qed.
Lemma lem3213249 {A : Type'} (_33012 : A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term175 A t s x) : term219 A t s _33012.
Proof. exact (EQ_MP (@lem3213246 A t s _33012) (@lem3213062 A _33012 t s x h1)). Qed.
Lemma lem3213250 {A : Type'} (_33012 : A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term175 A t s x) : term219 A t s _33012.
Proof. exact (@lem3213249 A _33012 t s x h1). Qed.
Lemma lem3213251 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term175 A t s x) : term219 A t s x.
Proof. exact (@lem3213250 A x t s x h1). Qed.
Lemma lem3213254 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term126 A t s x) (h2 : term175 A t s x) : s x.
Proof. exact (@lem3213251 A t s x h2 (@lem3213235 A t s x h1)). Qed.
Lemma lem3213255 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term126 A t s x) (h2 : term175 A t s x) : term211 A s x.
Proof. exact (fun h0 : term22 A s x => @lem3213254 A t s x h1 h2). Qed.
Lemma lem3213257 (p : Prop) : (term212 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3213258 {A : Type'} (s : A -> Prop) (x : A) : (term211 A s x) = (s x).
Proof. exact (@lem3213257 (s x)). Qed.
Lemma lem3213259 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term126 A t s x) (h2 : term175 A t s x) : s x.
Proof. exact (EQ_MP (@lem3213258 A s x) (@lem3213255 A t s x h1 h2)). Qed.
Lemma lem3213262 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3213264 {A : Type'} (s : A -> Prop) (x : A) : (term22 A s x) = (term213 A s x).
Proof. exact (@lem3213262 (s x)). Qed.
Lemma lem3213267 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term126 A t s x) : term213 A s x.
Proof. exact (EQ_MP (@lem3213264 A s x) (@lem3213072 A t s x h1)). Qed.
Lemma lem3213270 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term126 A t s x) (h2 : term175 A t s x) : False.
Proof. exact (@lem3213267 A t s x h1 (@lem3213259 A t s x h1 h2)). Qed.
Lemma lem3213271 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term126 A t s x) (h2 : term175 A t s x) : term214.
Proof. exact (fun h0 : ~ False => @lem3213270 A t s x h1 h2). Qed.
Lemma lem3213273 (p : Prop) : (term212 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3213274 : term214 = False.
Proof. exact (@lem3213273 False). Qed.
Lemma lem3213275 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term126 A t s x) (h2 : term175 A t s x) : False.
Proof. exact (EQ_MP (@lem3213274) (@lem3213271 A t s x h1 h2)). Qed.
Lemma lem3213277 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term66 A t s x) : s x.
Proof. exact (proj2 (@lem3212636 A t s x h1)). Qed.
Lemma lem3213278 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term66 A t s x) : term211 A s x.
Proof. exact (fun h0 : term22 A s x => @lem3213277 A t s x h1). Qed.
Lemma lem3213280 (p : Prop) : (term212 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3213281 {A : Type'} (s : A -> Prop) (x : A) : (term211 A s x) = (s x).
Proof. exact (@lem3213280 (s x)). Qed.
Lemma lem3213282 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term66 A t s x) : s x.
Proof. exact (EQ_MP (@lem3213281 A s x) (@lem3213278 A t s x h1)). Qed.
Lemma lem3213288 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3213289 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33015 : A) : (term104 A s t _33015) = (term100 A t s _33015).
Proof. exact (@lem3213288 (t _33015) (term22 A s _33015)). Qed.
Lemma lem3213295 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3213296 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33015 : A) : (term220 A s t _33015) = (term221 A t s _33015).
Proof. exact (MK_COMB (@lem3213295) (@lem3213289 A t s _33015)). Qed.
Lemma lem3213302 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33015 : A) : (term100 A t s _33015) = (term100 A t s _33015).
Proof. exact (eq_refl (term100 A t s _33015)). Qed.
Lemma lem3213303 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33015 : A) : ((term104 A s t _33015) = (term100 A t s _33015)) = ((term100 A t s _33015) = (term100 A t s _33015)).
Proof. exact (MK_COMB (@lem3213296 A t s _33015) (@lem3213302 A t s _33015)). Qed.
Lemma lem3213305 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3213306 (x : Prop) : (x = x) = True.
Proof. exact (@lem3213305 Prop x). Qed.
Lemma lem3213307 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33015 : A) : ((term100 A t s _33015) = (term100 A t s _33015)) = True.
Proof. exact (@lem3213306 (term100 A t s _33015)). Qed.
Lemma lem3213308 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33015 : A) : ((term104 A s t _33015) = (term100 A t s _33015)) = True.
Proof. exact (TRANS (@lem3213303 A t s _33015) (@lem3213307 A t s _33015)). Qed.
Lemma lem3213309 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33015 : A) : True = ((term104 A s t _33015) = (term100 A t s _33015)).
Proof. exact (SYM (@lem3213308 A t s _33015)). Qed.
Lemma lem3213310 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33015 : A) : (term104 A s t _33015) = (term100 A t s _33015).
Proof. exact (EQ_MP (@lem3213309 A t s _33015) (@lem0)). Qed.
Lemma lem3213311 {A : Type'} (_33015 : A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term175 A t s x) : term100 A t s _33015.
Proof. exact (EQ_MP (@lem3213310 A t s _33015) (@lem3213084 A _33015 t s x h1)). Qed.
Lemma lem3213313 (b : Prop) (a : Prop) : (a \/ b) = (term215 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3213314 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33015 : A) : (term100 A t s _33015) = (term216 A s t _33015).
Proof. exact (@lem3213313 (term22 A s _33015) (t _33015)). Qed.
Lemma lem3213316 (a : Prop) : (term37 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3213317 {A : Type'} (s : A -> Prop) (_33015 : A) : (term54 A s _33015) = (s _33015).
Proof. exact (@lem3213316 (s _33015)). Qed.
Lemma lem3213318 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3213319 {A : Type'} (s : A -> Prop) (_33015 : A) : (term217 A s _33015) = (term218 A s _33015).
Proof. exact (MK_COMB (@lem3213318) (@lem3213317 A s _33015)). Qed.
Lemma lem3213320 {A : Type'} (t : A -> Prop) (_33015 : A) : (t _33015) = (t _33015).
Proof. exact (eq_refl (t _33015)). Qed.
Lemma lem3213321 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33015 : A) : (term216 A s t _33015) = (term219 A s t _33015).
Proof. exact (MK_COMB (@lem3213319 A s _33015) (@lem3213320 A t _33015)). Qed.
Lemma lem3213322 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33015 : A) : (term100 A t s _33015) = (term219 A s t _33015).
Proof. exact (TRANS (@lem3213314 A s t _33015) (@lem3213321 A s t _33015)). Qed.
Lemma lem3213325 {A : Type'} (_33015 : A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term175 A t s x) : term219 A s t _33015.
Proof. exact (EQ_MP (@lem3213322 A s t _33015) (@lem3213311 A _33015 t s x h1)). Qed.
Lemma lem3213326 {A : Type'} (_33015 : A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term175 A t s x) : term219 A s t _33015.
Proof. exact (@lem3213325 A _33015 t s x h1). Qed.
Lemma lem3213327 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term175 A t s x) : term219 A s t x.
Proof. exact (@lem3213326 A x t s x h1). Qed.
Lemma lem3213330 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term66 A t s x) (h2 : term175 A t s x) : t x.
Proof. exact (@lem3213327 A t s x h2 (@lem3213282 A t s x h1)). Qed.
Lemma lem3213331 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term66 A t s x) (h2 : term175 A t s x) : term211 A t x.
Proof. exact (fun h0 : term22 A t x => @lem3213330 A t s x h1 h2). Qed.
Lemma lem3213333 (p : Prop) : (term212 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3213334 {A : Type'} (t : A -> Prop) (x : A) : (term211 A t x) = (t x).
Proof. exact (@lem3213333 (t x)). Qed.
Lemma lem3213335 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term66 A t s x) (h2 : term175 A t s x) : t x.
Proof. exact (EQ_MP (@lem3213334 A t x) (@lem3213331 A t s x h1 h2)). Qed.
Lemma lem3213338 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3213340 {A : Type'} (t : A -> Prop) (x : A) : (term22 A t x) = (term213 A t x).
Proof. exact (@lem3213338 (t x)). Qed.
Lemma lem3213343 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term66 A t s x) : term213 A t x.
Proof. exact (EQ_MP (@lem3213340 A t x) (@lem3213086 A t s x h1)). Qed.
Lemma lem3213346 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term66 A t s x) (h2 : term175 A t s x) : False.
Proof. exact (@lem3213343 A t s x h1 (@lem3213335 A t s x h1 h2)). Qed.
Lemma lem3213347 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term66 A t s x) (h2 : term175 A t s x) : term214.
Proof. exact (fun h0 : ~ False => @lem3213346 A t s x h1 h2). Qed.
Lemma lem3213349 (p : Prop) : (term212 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3213350 : term214 = False.
Proof. exact (@lem3213349 False). Qed.
Lemma lem3213351 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term66 A t s x) (h2 : term175 A t s x) : False.
Proof. exact (EQ_MP (@lem3213350) (@lem3213347 A t s x h1 h2)). Qed.
Lemma lem3213352 {A : Type'} (t : A -> Prop) (x : A) (h1 : term22 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3213228 A t x h1 h2) (fun h3 : False => @lem3213032 A t x h2)). Qed.
Lemma lem3213353 {A : Type'} (t : A -> Prop) (x : A) (h1 : term22 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3213352 A t x h1 h2) (@lem3213032 A t x h2)). Qed.
Lemma lem3213354 {A : Type'} (t : A -> Prop) (x : A) (h1 : term22 A t x) (h2 : t x) : (term22 A t x) = False.
Proof. exact (prop_ext (fun h3 : term22 A t x => @lem3213353 A t x h1 h2) (fun h3 : False => @lem3213030 A t x h1)). Qed.
Lemma lem3213355 {A : Type'} (t : A -> Prop) (x : A) (h1 : term22 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3213354 A t x h1 h2) (@lem3213030 A t x h1)). Qed.
Lemma lem3213356 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A t x) (h2 : s x) (h3 : term157 A x t s) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3213205 A x t s h1 h2 h3) (fun h4 : False => @lem3213004 A s x h2)). Qed.
Lemma lem3213357 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A t x) (h2 : s x) (h3 : term157 A x t s) : False.
Proof. exact (EQ_MP (@lem3213356 A x t s h1 h2 h3) (@lem3213004 A s x h2)). Qed.
Lemma lem3213358 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A t x) (h2 : s x) (h3 : term157 A x t s) : (term22 A t x) = False.
Proof. exact (prop_ext (fun h4 : term22 A t x => @lem3213357 A x t s h1 h2 h3) (fun h4 : False => @lem3213002 A t x h1)). Qed.
Lemma lem3213359 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A t x) (h2 : s x) (h3 : term157 A x t s) : False.
Proof. exact (EQ_MP (@lem3213358 A x t s h1 h2 h3) (@lem3213002 A t x h1)). Qed.
Lemma lem3213360 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A s x) (h2 : t x) (h3 : term157 A x t s) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3213158 A x t s h1 h2 h3) (fun h4 : False => @lem3212976 A t x h2)). Qed.
Lemma lem3213361 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A s x) (h2 : t x) (h3 : term157 A x t s) : False.
Proof. exact (EQ_MP (@lem3213360 A x t s h1 h2 h3) (@lem3212976 A t x h2)). Qed.
Lemma lem3213362 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A s x) (h2 : t x) (h3 : term157 A x t s) : (term22 A s x) = False.
Proof. exact (prop_ext (fun h4 : term22 A s x => @lem3213361 A x t s h1 h2 h3) (fun h4 : False => @lem3212974 A s x h1)). Qed.
Lemma lem3213363 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A s x) (h2 : t x) (h3 : term157 A x t s) : False.
Proof. exact (EQ_MP (@lem3213362 A x t s h1 h2 h3) (@lem3212974 A s x h1)). Qed.
Lemma lem3213364 {A : Type'} (s : A -> Prop) (x : A) (h1 : term22 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3213111 A s x h1 h2) (fun h3 : False => @lem3212948 A s x h2)). Qed.
Lemma lem3213365 {A : Type'} (s : A -> Prop) (x : A) (h1 : term22 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3213364 A s x h1 h2) (@lem3212948 A s x h2)). Qed.
Lemma lem3213366 {A : Type'} (s : A -> Prop) (x : A) (h1 : term22 A s x) (h2 : s x) : (term22 A s x) = False.
Proof. exact (prop_ext (fun h3 : term22 A s x => @lem3213365 A s x h1 h2) (fun h3 : False => @lem3212946 A s x h1)). Qed.
Lemma lem3213367 {A : Type'} (s : A -> Prop) (x : A) (h1 : term22 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3213366 A s x h1 h2) (@lem3212946 A s x h1)). Qed.
Lemma lem3213368 {A : Type'} (t : A -> Prop) (x : A) (h1 : term22 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3213355 A t x h1 h2) (fun h3 : False => @lem3212828 A t x h2)). Qed.
Lemma lem3213369 {A : Type'} (t : A -> Prop) (x : A) (h1 : term22 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3213368 A t x h1 h2) (@lem3212828 A t x h2)). Qed.
Lemma lem3213370 {A : Type'} (t : A -> Prop) (x : A) (h1 : term22 A t x) (h2 : t x) : (term22 A t x) = False.
Proof. exact (prop_ext (fun h3 : term22 A t x => @lem3213369 A t x h1 h2) (fun h3 : False => @lem3212824 A t x h1)). Qed.
Lemma lem3213371 {A : Type'} (t : A -> Prop) (x : A) (h1 : term22 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3213370 A t x h1 h2) (@lem3212824 A t x h1)). Qed.
Lemma lem3213372 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A t x) (h2 : s x) (h3 : term157 A x t s) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3213359 A x t s h1 h2 h3) (fun h4 : False => @lem3212781 A s x h2)). Qed.
Lemma lem3213373 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A t x) (h2 : s x) (h3 : term157 A x t s) : False.
Proof. exact (EQ_MP (@lem3213372 A x t s h1 h2 h3) (@lem3212781 A s x h2)). Qed.
Lemma lem3213374 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A t x) (h2 : s x) (h3 : term157 A x t s) : (term22 A t x) = False.
Proof. exact (prop_ext (fun h4 : term22 A t x => @lem3213373 A x t s h1 h2 h3) (fun h4 : False => @lem3212777 A t x h1)). Qed.
Lemma lem3213375 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A t x) (h2 : s x) (h3 : term157 A x t s) : False.
Proof. exact (EQ_MP (@lem3213374 A x t s h1 h2 h3) (@lem3212777 A t x h1)). Qed.
Lemma lem3213376 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A s x) (h2 : t x) (h3 : term157 A x t s) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3213363 A x t s h1 h2 h3) (fun h4 : False => @lem3212734 A t x h2)). Qed.
Lemma lem3213377 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A s x) (h2 : t x) (h3 : term157 A x t s) : False.
Proof. exact (EQ_MP (@lem3213376 A x t s h1 h2 h3) (@lem3212734 A t x h2)). Qed.
Lemma lem3213378 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A s x) (h2 : t x) (h3 : term157 A x t s) : (term22 A s x) = False.
Proof. exact (prop_ext (fun h4 : term22 A s x => @lem3213377 A x t s h1 h2 h3) (fun h4 : False => @lem3212730 A s x h1)). Qed.
Lemma lem3213379 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A s x) (h2 : t x) (h3 : term157 A x t s) : False.
Proof. exact (EQ_MP (@lem3213378 A x t s h1 h2 h3) (@lem3212730 A s x h1)). Qed.
Lemma lem3213380 {A : Type'} (s : A -> Prop) (x : A) (h1 : term22 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3213367 A s x h1 h2) (fun h3 : False => @lem3212687 A s x h2)). Qed.
Lemma lem3213381 {A : Type'} (s : A -> Prop) (x : A) (h1 : term22 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3213380 A s x h1 h2) (@lem3212687 A s x h2)). Qed.
Lemma lem3213382 {A : Type'} (s : A -> Prop) (x : A) (h1 : term22 A s x) (h2 : s x) : (term22 A s x) = False.
Proof. exact (prop_ext (fun h3 : term22 A s x => @lem3213381 A s x h1 h2) (fun h3 : False => @lem3212683 A s x h1)). Qed.
Lemma lem3213383 {A : Type'} (s : A -> Prop) (x : A) (h1 : term22 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3213382 A s x h1 h2) (@lem3212683 A s x h1)). Qed.
Lemma lem3213384 {A : Type'} (t : A -> Prop) (x : A) (h1 : term22 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3213371 A t x h1 h2) (fun h3 : False => @lem3212828 A t x h2)). Qed.
Lemma lem3213385 {A : Type'} (t : A -> Prop) (x : A) (h1 : term22 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3213384 A t x h1 h2) (@lem3212828 A t x h2)). Qed.
Lemma lem3213386 {A : Type'} (t : A -> Prop) (x : A) (h1 : term22 A t x) (h2 : t x) : (term22 A t x) = False.
Proof. exact (prop_ext (fun h3 : term22 A t x => @lem3213385 A t x h1 h2) (fun h3 : False => @lem3212824 A t x h1)). Qed.
Lemma lem3213387 {A : Type'} (t : A -> Prop) (x : A) (h1 : term22 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3213386 A t x h1 h2) (@lem3212824 A t x h1)). Qed.
Lemma lem3213388 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A t x) (h2 : s x) (h3 : term157 A x t s) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3213375 A x t s h1 h2 h3) (fun h4 : False => @lem3212781 A s x h2)). Qed.
Lemma lem3213389 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A t x) (h2 : s x) (h3 : term157 A x t s) : False.
Proof. exact (EQ_MP (@lem3213388 A x t s h1 h2 h3) (@lem3212781 A s x h2)). Qed.
Lemma lem3213390 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A t x) (h2 : s x) (h3 : term157 A x t s) : (term22 A t x) = False.
Proof. exact (prop_ext (fun h4 : term22 A t x => @lem3213389 A x t s h1 h2 h3) (fun h4 : False => @lem3212777 A t x h1)). Qed.
Lemma lem3213391 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A t x) (h2 : s x) (h3 : term157 A x t s) : False.
Proof. exact (EQ_MP (@lem3213390 A x t s h1 h2 h3) (@lem3212777 A t x h1)). Qed.
Lemma lem3213392 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A s x) (h2 : t x) (h3 : term157 A x t s) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3213379 A x t s h1 h2 h3) (fun h4 : False => @lem3212734 A t x h2)). Qed.
Lemma lem3213393 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A s x) (h2 : t x) (h3 : term157 A x t s) : False.
Proof. exact (EQ_MP (@lem3213392 A x t s h1 h2 h3) (@lem3212734 A t x h2)). Qed.
Lemma lem3213394 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A s x) (h2 : t x) (h3 : term157 A x t s) : (term22 A s x) = False.
Proof. exact (prop_ext (fun h4 : term22 A s x => @lem3213393 A x t s h1 h2 h3) (fun h4 : False => @lem3212730 A s x h1)). Qed.
Lemma lem3213395 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A s x) (h2 : t x) (h3 : term157 A x t s) : False.
Proof. exact (EQ_MP (@lem3213394 A x t s h1 h2 h3) (@lem3212730 A s x h1)). Qed.
Lemma lem3213396 {A : Type'} (s : A -> Prop) (x : A) (h1 : term22 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3213383 A s x h1 h2) (fun h3 : False => @lem3212687 A s x h2)). Qed.
Lemma lem3213397 {A : Type'} (s : A -> Prop) (x : A) (h1 : term22 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3213396 A s x h1 h2) (@lem3212687 A s x h2)). Qed.
Lemma lem3213398 {A : Type'} (s : A -> Prop) (x : A) (h1 : term22 A s x) (h2 : s x) : (term22 A s x) = False.
Proof. exact (prop_ext (fun h3 : term22 A s x => @lem3213397 A s x h1 h2) (fun h3 : False => @lem3212683 A s x h1)). Qed.
Lemma lem3213399 {A : Type'} (s : A -> Prop) (x : A) (h1 : term22 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3213398 A s x h1 h2) (@lem3212683 A s x h1)). Qed.
Lemma lem3213400 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term175 A t s x) : False.
Proof. exact (or_elim (@lem3212631 A t s x h1) (fun h0 : term126 A t s x => @lem3213275 A t s x h0 h1) (fun h0 : term66 A t s x => @lem3213351 A t s x h0 h1)). Qed.
Lemma lem3213401 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A t x) (h2 : term157 A x t s) : False.
Proof. exact (or_elim (@lem3212624 A x t s h2) (fun h0 : s x => @lem3213391 A x t s h1 h0 h2) (fun h0 : t x => @lem3213387 A t x h1 h0)). Qed.
Lemma lem3213402 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term22 A s x) (h2 : term157 A x t s) : False.
Proof. exact (or_elim (@lem3212624 A x t s h2) (fun h0 : s x => @lem3213399 A s x h1 h0) (fun h0 : t x => @lem3213395 A x t s h1 h0 h2)). Qed.
Lemma lem3213403 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term157 A x t s) : False.
Proof. exact (or_elim (@lem3212623 A x t s h1) (fun h0 : term22 A s x => @lem3213402 A x t s h0 h1) (fun h0 : term22 A t x => @lem3213401 A x t s h0 h1)). Qed.
Lemma lem3213404 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term194 A t s x) : False.
Proof. exact (or_elim (@lem3212618 A t s x h1) (fun h0 : term157 A x t s => @lem3213403 A x t s h0) (fun h0 : term175 A t s x => @lem3213400 A t s x h0)). Qed.
Lemma lem3213405 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term194 A t s x) : (term194 A t s x) = False.
Proof. exact (prop_ext (fun h2 : term194 A t s x => @lem3213404 A t s x h1) (fun h2 : False => @lem3212618 A t s x h1)). Qed.
Lemma lem3213406 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term194 A t s x) : False.
Proof. exact (EQ_MP (@lem3213405 A t s x h1) (@lem3212618 A t s x h1)). Qed.
Lemma lem3213407 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term39 A t s) : False.
Proof. exact (ex_elim (@lem3212498 A t s h1) (fun x : A => fun h0 : term196 A t s x => @lem3213406 A t s x h0)). Qed.
Lemma lem3213408 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term39 A t s) : (term39 A t s) = False.
Proof. exact (prop_ext (fun h2 : term39 A t s => @lem3213407 A t s h1) (fun h2 : False => @lem3212022 A t s h1)). Qed.
Lemma lem3213409 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term39 A t s) : False.
Proof. exact (EQ_MP (@lem3213408 A t s h1) (@lem3212022 A t s h1)). Qed.
Lemma lem3213410 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term38 A t s.
Proof. exact (fun h0 : term39 A t s => @lem3213409 A t s h0). Qed.
Lemma lem3213411 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term19 A s t) = (term25 A t s).
Proof. exact (EQ_MP (@lem3212021 A t s) (@lem3213410 A t s)). Qed.
Lemma lem3213416 {A : Type'} (s : A -> Prop) : term27 A s.
Proof. exact (fun t : A -> Prop => @lem3213411 A t s). Qed.
Lemma lem3213421 {A : Type'} : term29 A.
Proof. exact (fun s : A -> Prop => @lem3213416 A s). Qed.
Lemma lem3213422 {A : Type'} : term31 A.
Proof. exact (EQ_MP (@lem3212017 A) (@lem3213421 A)). Qed.
Lemma lem3213424 {A : Type'} : term31 A.
Proof. exact (@lem3211933 A (@lem3213422 A)). Qed.
Lemma lem3213425 {A : Type'} (h1 : term32 A) : False.
Proof. exact (@lem3213424 A (@lem3211917 A h1)). Qed.
Lemma lem3213426 {A : Type'} (h1 : term32 A) : (term32 A) = False.
Proof. exact (prop_ext (fun h2 : term32 A => @lem3213425 A h1) (fun h2 : False => @lem3211917 A h1)). Qed.
Lemma lem3213427 {A : Type'} (h1 : term32 A) : False.
Proof. exact (EQ_MP (@lem3213426 A h1) (@lem3211917 A h1)). Qed.
Lemma lem3213428 {A : Type'} : term31 A.
Proof. exact (fun h0 : term32 A => @lem3213427 A h0). Qed.
Lemma lem3213429 {A : Type'} : term29 A.
Proof. exact (EQ_MP (@lem3211916 A) (@lem3213428 A)). Qed.
Lemma lem3213430 {A : Type'} : term13 A.
Proof. exact (EQ_MP (@lem3211912 A) (@lem3213429 A)). Qed.
Lemma lem3213431 {A : Type'} : term12 A.
Proof. exact (EQ_MP (@lem3211826 A) (@lem3213430 A)). Qed.
