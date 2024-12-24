Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNIONS_UNION_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211662_spec.
Require Import thm3211663_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3343835 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3343836 {_87099 : Type'} (s : _87099 -> Prop) (t : _87099 -> Prop) : (s = t) = (term0 _87099 s t).
Proof. exact (@lem3343835 _87099 s t). Qed.
Lemma lem3343837 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) : ((term1 _87099 s t) = (term2 _87099 s t)) = (term3 _87099 s t).
Proof. exact (@lem3343836 _87099 (term1 _87099 s t) (term2 _87099 s t)). Qed.
Lemma lem3343846 {_87099 : Type'} (s : type686 _87099) : (term4 _87099 s) = (term5 _87099 s).
Proof. exact (fun_ext (fun t : type686 _87099 => @lem3343837 _87099 s t)). Qed.
Lemma lem3343847 {_87099 : Type'} : (@all ((_87099 -> Prop) -> Prop)) = (@all ((_87099 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87099 -> Prop) -> Prop))). Qed.
Lemma lem3343848 {_87099 : Type'} (s : type686 _87099) : (term6 _87099 s) = (term7 _87099 s).
Proof. exact (MK_COMB (@lem3343847 _87099) (@lem3343846 _87099 s)). Qed.
Lemma lem3343853 {_87099 : Type'} : (term8 _87099) = (term9 _87099).
Proof. exact (fun_ext (fun s : type686 _87099 => @lem3343848 _87099 s)). Qed.
Lemma lem3343854 {_87099 : Type'} : (@all ((_87099 -> Prop) -> Prop)) = (@all ((_87099 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87099 -> Prop) -> Prop))). Qed.
Lemma lem3343855 {_87099 : Type'} : (term10 _87099) = (term11 _87099).
Proof. exact (MK_COMB (@lem3343854 _87099) (@lem3343853 _87099)). Qed.
Lemma lem3343860 {_87099 : Type'} : (term11 _87099) = (term10 _87099).
Proof. exact (SYM (@lem3343855 _87099)). Qed.
Lemma lem3343876 {A : Type'} (s : type686 A) (x : A) : (term12 A x s) = (term13 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3343877 {_87099 : Type'} (s : type686 _87099) (x : _87099) : (term12 _87099 x s) = (term13 _87099 s x).
Proof. exact (@lem3343876 _87099 s x). Qed.
Lemma lem3343878 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term14 _87099 x s t) = (term15 _87099 s t x).
Proof. exact (@lem3343877 _87099 (@UNION (_87099 -> Prop) s t) x). Qed.
Lemma lem3343886 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3343887 {_87099 : Type'} (s : type686 _87099) (x : _87099 -> Prop) (t : type686 _87099) : (term18 _87099 x s t) = (term19 _87099 s x t).
Proof. exact (@lem3343886 (_87099 -> Prop) s x t). Qed.
Lemma lem3343888 {_87099 : Type'} (s : type686 _87099) (t : _87099 -> Prop) (t' : type686 _87099) : (term18 _87099 t s t') = (term19 _87099 s t t').
Proof. exact (@lem3343887 _87099 s t t'). Qed.
Lemma lem3343892 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3343893 {_87099 : Type'} (P : type686 _87099) (x : _87099 -> Prop) : (@IN (_87099 -> Prop) x P) = (P x).
Proof. exact (@lem3343892 (_87099 -> Prop) P x). Qed.
Lemma lem3343894 {_87099 : Type'} (s : type686 _87099) (t : _87099 -> Prop) : (@IN (_87099 -> Prop) t s) = (s t).
Proof. exact (@lem3343893 _87099 s t). Qed.
Lemma lem3343895 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3343896 {_87099 : Type'} (s : type686 _87099) (t : _87099 -> Prop) : (term20 _87099 t s) = (term21 _87099 s t).
Proof. exact (MK_COMB (@lem3343895) (@lem3343894 _87099 s t)). Qed.
Lemma lem3343898 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3343899 {_87099 : Type'} (P : type686 _87099) (x : _87099 -> Prop) : (@IN (_87099 -> Prop) x P) = (P x).
Proof. exact (@lem3343898 (_87099 -> Prop) P x). Qed.
Lemma lem3343900 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) : (@IN (_87099 -> Prop) t' t) = (t t').
Proof. exact (@lem3343899 _87099 t t'). Qed.
Lemma lem3343901 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) : (term19 _87099 s t' t) = (term22 _87099 s t t').
Proof. exact (MK_COMB (@lem3343896 _87099 s t') (@lem3343900 _87099 t t')). Qed.
Lemma lem3343904 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) : (term18 _87099 t' s t) = (term22 _87099 s t t').
Proof. exact (TRANS (@lem3343888 _87099 s t' t) (@lem3343901 _87099 s t t')). Qed.
Lemma lem3343905 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3343906 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) : (term23 _87099 t' s t) = (term24 _87099 s t t').
Proof. exact (MK_COMB (@lem3343905) (@lem3343904 _87099 s t t')). Qed.
Lemma lem3343908 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3343909 {_87099 : Type'} (P : _87099 -> Prop) (x : _87099) : (@IN _87099 x P) = (P x).
Proof. exact (@lem3343908 _87099 P x). Qed.
Lemma lem3343910 {_87099 : Type'} (t : _87099 -> Prop) (x : _87099) : (@IN _87099 x t) = (t x).
Proof. exact (@lem3343909 _87099 t x). Qed.
Lemma lem3343911 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term25 _87099 s t x t') = (term26 _87099 s t t' x).
Proof. exact (MK_COMB (@lem3343906 _87099 s t t') (@lem3343910 _87099 t' x)). Qed.
Lemma lem3343914 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term27 _87099 s t x) = (term28 _87099 s t x).
Proof. exact (fun_ext (fun t' : _87099 -> Prop => @lem3343911 _87099 s t t' x)). Qed.
Lemma lem3343915 {_87099 : Type'} : (@ex (_87099 -> Prop)) = (@ex (_87099 -> Prop)).
Proof. exact (eq_refl (@ex (_87099 -> Prop))). Qed.
Lemma lem3343916 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term15 _87099 s t x) = (term29 _87099 s t x).
Proof. exact (MK_COMB (@lem3343915 _87099) (@lem3343914 _87099 s t x)). Qed.
Lemma lem3343921 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term14 _87099 x s t) = (term29 _87099 s t x).
Proof. exact (TRANS (@lem3343878 _87099 s t x) (@lem3343916 _87099 s t x)). Qed.
Lemma lem3343922 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3343923 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term30 _87099 x s t) = (term31 _87099 s t x).
Proof. exact (MK_COMB (@lem3343922) (@lem3343921 _87099 s t x)). Qed.
Lemma lem3343925 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3343926 {_87099 : Type'} (s : _87099 -> Prop) (x : _87099) (t : _87099 -> Prop) : (term16 _87099 x s t) = (term17 _87099 s x t).
Proof. exact (@lem3343925 _87099 s x t). Qed.
Lemma lem3343927 {_87099 : Type'} (s : type686 _87099) (x : _87099) (t : type686 _87099) : (term32 _87099 x s t) = (term33 _87099 s x t).
Proof. exact (@lem3343926 _87099 (@UNIONS _87099 s) x (@UNIONS _87099 t)). Qed.
Lemma lem3343931 {A : Type'} (s : type686 A) (x : A) : (term12 A x s) = (term13 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3343932 {_87099 : Type'} (s : type686 _87099) (x : _87099) : (term12 _87099 x s) = (term13 _87099 s x).
Proof. exact (@lem3343931 _87099 s x). Qed.
Lemma lem3343940 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3343941 {_87099 : Type'} (P : type686 _87099) (x : _87099 -> Prop) : (@IN (_87099 -> Prop) x P) = (P x).
Proof. exact (@lem3343940 (_87099 -> Prop) P x). Qed.
Lemma lem3343942 {_87099 : Type'} (s : type686 _87099) (t : _87099 -> Prop) : (@IN (_87099 -> Prop) t s) = (s t).
Proof. exact (@lem3343941 _87099 s t). Qed.
Lemma lem3343943 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3343944 {_87099 : Type'} (s : type686 _87099) (t : _87099 -> Prop) : (term34 _87099 t s) = (term35 _87099 s t).
Proof. exact (MK_COMB (@lem3343943) (@lem3343942 _87099 s t)). Qed.
Lemma lem3343946 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3343947 {_87099 : Type'} (P : _87099 -> Prop) (x : _87099) : (@IN _87099 x P) = (P x).
Proof. exact (@lem3343946 _87099 P x). Qed.
Lemma lem3343948 {_87099 : Type'} (t : _87099 -> Prop) (x : _87099) : (@IN _87099 x t) = (t x).
Proof. exact (@lem3343947 _87099 t x). Qed.
Lemma lem3343949 {_87099 : Type'} (s : type686 _87099) (t : _87099 -> Prop) (x : _87099) : (term36 _87099 s x t) = (term37 _87099 s t x).
Proof. exact (MK_COMB (@lem3343944 _87099 s t) (@lem3343948 _87099 t x)). Qed.
Lemma lem3343952 {_87099 : Type'} (s : type686 _87099) (x : _87099) : (term38 _87099 s x) = (term39 _87099 s x).
Proof. exact (fun_ext (fun t : _87099 -> Prop => @lem3343949 _87099 s t x)). Qed.
Lemma lem3343953 {_87099 : Type'} : (@ex (_87099 -> Prop)) = (@ex (_87099 -> Prop)).
Proof. exact (eq_refl (@ex (_87099 -> Prop))). Qed.
Lemma lem3343954 {_87099 : Type'} (s : type686 _87099) (x : _87099) : (term13 _87099 s x) = (term40 _87099 s x).
Proof. exact (MK_COMB (@lem3343953 _87099) (@lem3343952 _87099 s x)). Qed.
Lemma lem3343959 {_87099 : Type'} (s : type686 _87099) (x : _87099) : (term12 _87099 x s) = (term40 _87099 s x).
Proof. exact (TRANS (@lem3343932 _87099 s x) (@lem3343954 _87099 s x)). Qed.
Lemma lem3343960 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3343961 {_87099 : Type'} (s : type686 _87099) (x : _87099) : (term41 _87099 x s) = (term42 _87099 s x).
Proof. exact (MK_COMB (@lem3343960) (@lem3343959 _87099 s x)). Qed.
Lemma lem3343963 {A : Type'} (s : type686 A) (x : A) : (term12 A x s) = (term13 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3343964 {_87099 : Type'} (s : type686 _87099) (x : _87099) : (term12 _87099 x s) = (term13 _87099 s x).
Proof. exact (@lem3343963 _87099 s x). Qed.
Lemma lem3343965 {_87099 : Type'} (t : type686 _87099) (x : _87099) : (term12 _87099 x t) = (term13 _87099 t x).
Proof. exact (@lem3343964 _87099 t x). Qed.
Lemma lem3343973 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3343974 {_87099 : Type'} (P : type686 _87099) (x : _87099 -> Prop) : (@IN (_87099 -> Prop) x P) = (P x).
Proof. exact (@lem3343973 (_87099 -> Prop) P x). Qed.
Lemma lem3343975 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) : (@IN (_87099 -> Prop) t' t) = (t t').
Proof. exact (@lem3343974 _87099 t t'). Qed.
Lemma lem3343976 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3343977 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) : (term34 _87099 t' t) = (term35 _87099 t t').
Proof. exact (MK_COMB (@lem3343976) (@lem3343975 _87099 t t')). Qed.
Lemma lem3343979 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3343980 {_87099 : Type'} (P : _87099 -> Prop) (x : _87099) : (@IN _87099 x P) = (P x).
Proof. exact (@lem3343979 _87099 P x). Qed.
Lemma lem3343981 {_87099 : Type'} (t : _87099 -> Prop) (x : _87099) : (@IN _87099 x t) = (t x).
Proof. exact (@lem3343980 _87099 t x). Qed.
Lemma lem3343982 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term36 _87099 t x t') = (term37 _87099 t t' x).
Proof. exact (MK_COMB (@lem3343977 _87099 t t') (@lem3343981 _87099 t' x)). Qed.
Lemma lem3343985 {_87099 : Type'} (t : type686 _87099) (x : _87099) : (term38 _87099 t x) = (term39 _87099 t x).
Proof. exact (fun_ext (fun t' : _87099 -> Prop => @lem3343982 _87099 t t' x)). Qed.
Lemma lem3343986 {_87099 : Type'} : (@ex (_87099 -> Prop)) = (@ex (_87099 -> Prop)).
Proof. exact (eq_refl (@ex (_87099 -> Prop))). Qed.
Lemma lem3343987 {_87099 : Type'} (t : type686 _87099) (x : _87099) : (term13 _87099 t x) = (term40 _87099 t x).
Proof. exact (MK_COMB (@lem3343986 _87099) (@lem3343985 _87099 t x)). Qed.
Lemma lem3343992 {_87099 : Type'} (t : type686 _87099) (x : _87099) : (term12 _87099 x t) = (term40 _87099 t x).
Proof. exact (TRANS (@lem3343965 _87099 t x) (@lem3343987 _87099 t x)). Qed.
Lemma lem3343993 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term33 _87099 s x t) = (term43 _87099 s t x).
Proof. exact (MK_COMB (@lem3343961 _87099 s x) (@lem3343992 _87099 t x)). Qed.
Lemma lem3343996 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term32 _87099 x s t) = (term43 _87099 s t x).
Proof. exact (TRANS (@lem3343927 _87099 s x t) (@lem3343993 _87099 s t x)). Qed.
Lemma lem3343997 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : ((term14 _87099 x s t) = (term32 _87099 x s t)) = ((term29 _87099 s t x) = (term43 _87099 s t x)).
Proof. exact (MK_COMB (@lem3343923 _87099 s t x) (@lem3343996 _87099 s t x)). Qed.
Lemma lem3344000 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) : (term44 _87099 s t) = (term45 _87099 s t).
Proof. exact (fun_ext (fun x : _87099 => @lem3343997 _87099 s t x)). Qed.
Lemma lem3344001 {_87099 : Type'} : (@all _87099) = (@all _87099).
Proof. exact (eq_refl (@all _87099)). Qed.
Lemma lem3344002 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) : (term3 _87099 s t) = (term46 _87099 s t).
Proof. exact (MK_COMB (@lem3344001 _87099) (@lem3344000 _87099 s t)). Qed.
Lemma lem3344007 {_87099 : Type'} (s : type686 _87099) : (term5 _87099 s) = (term47 _87099 s).
Proof. exact (fun_ext (fun t : type686 _87099 => @lem3344002 _87099 s t)). Qed.
Lemma lem3344008 {_87099 : Type'} : (@all ((_87099 -> Prop) -> Prop)) = (@all ((_87099 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87099 -> Prop) -> Prop))). Qed.
Lemma lem3344009 {_87099 : Type'} (s : type686 _87099) : (term7 _87099 s) = (term48 _87099 s).
Proof. exact (MK_COMB (@lem3344008 _87099) (@lem3344007 _87099 s)). Qed.
Lemma lem3344014 {_87099 : Type'} : (term9 _87099) = (term49 _87099).
Proof. exact (fun_ext (fun s : type686 _87099 => @lem3344009 _87099 s)). Qed.
Lemma lem3344015 {_87099 : Type'} : (@all ((_87099 -> Prop) -> Prop)) = (@all ((_87099 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87099 -> Prop) -> Prop))). Qed.
Lemma lem3344016 {_87099 : Type'} : (term11 _87099) = (term50 _87099).
Proof. exact (MK_COMB (@lem3344015 _87099) (@lem3344014 _87099)). Qed.
Lemma lem3344021 {_87099 : Type'} : (term50 _87099) = (term11 _87099).
Proof. exact (SYM (@lem3344016 _87099)). Qed.
Lemma lem3344023 (p : Prop) : p = (term51 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3344024 {_87099 : Type'} : (term50 _87099) = (term52 _87099).
Proof. exact (@lem3344023 (term50 _87099)). Qed.
Lemma lem3344025 {_87099 : Type'} : (term52 _87099) = (term50 _87099).
Proof. exact (SYM (@lem3344024 _87099)). Qed.
Lemma lem3344026 {_87099 : Type'} (h1 : term53 _87099) : term53 _87099.
Proof. exact (h1). Qed.
Lemma lem3344029 {_87099 : Type'} (h1 : term52 _87099) : term52 _87099.
Proof. exact (h1). Qed.
Lemma lem3344030 {_87099 : Type'} : term54 _87099.
Proof. exact (fun h0 : term52 _87099 => @lem3344029 _87099 h0). Qed.
Lemma lem3344031 {_87099 : Type'} (h1 : term54 _87099) : term54 _87099.
Proof. exact (h1). Qed.
Lemma lem3344032 {_87099 : Type'} (h1 : term52 _87099) : term52 _87099.
Proof. exact (h1). Qed.
Lemma lem3344033 {_87099 : Type'} (h1 : term52 _87099) (h2 : term54 _87099) : term52 _87099.
Proof. exact (@lem3344031 _87099 h2 (@lem3344032 _87099 h1)). Qed.
Lemma lem3344034 {_87099 : Type'} (h1 : term52 _87099) : term55 _87099.
Proof. exact (fun h0 : term54 _87099 => @lem3344033 _87099 h1 h0). Qed.
Lemma lem3344035 {_87099 : Type'} (h1 : term54 _87099) : term54 _87099.
Proof. exact (h1). Qed.
Lemma lem3344036 {_87099 : Type'} (h1 : term52 _87099) (h2 : term54 _87099) : term52 _87099.
Proof. exact (@lem3344034 _87099 h1 (@lem3344035 _87099 h2)). Qed.
Lemma lem3344037 {_87099 : Type'} (h1 : term54 _87099) : term54 _87099.
Proof. exact (fun h0 : term52 _87099 => @lem3344036 _87099 h0 h1). Qed.
Lemma lem3344038 {_87099 : Type'} : term56 _87099.
Proof. exact (fun h0 : term54 _87099 => @lem3344037 _87099 h0). Qed.
Lemma lem3344041 {_87099 : Type'} : term54 _87099.
Proof. exact (@lem3344038 _87099 (@lem3344030 _87099)). Qed.
Lemma lem3344042 {_87099 : Type'} : term54 _87099.
Proof. exact (@lem3344041 _87099). Qed.
Lemma lem3344044 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3344045 {_87099 : Type'} : (term52 _87099) = (term57 _87099).
Proof. exact (@lem3344044 (term53 _87099)). Qed.
Lemma lem3344047 (t : Prop) : (term58 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3344048 {_87099 : Type'} : (term57 _87099) = (term50 _87099).
Proof. exact (@lem3344047 (term50 _87099)). Qed.
Lemma lem3344179 {_87099 : Type'} : (term52 _87099) = (term50 _87099).
Proof. exact (TRANS (@lem3344045 _87099) (@lem3344048 _87099)). Qed.
Lemma lem3344184 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term37 _87099 t t' x) = (term37 _87099 t t' x).
Proof. exact (eq_refl (term37 _87099 t t' x)). Qed.
Lemma lem3344185 {_87099 : Type'} (t : type686 _87099) (x : _87099) : (term39 _87099 t x) = (term39 _87099 t x).
Proof. exact (fun_ext (fun t' : _87099 -> Prop => @lem3344184 _87099 t t' x)). Qed.
Lemma lem3344186 {_87099 : Type'} : (@ex (_87099 -> Prop)) = (@ex (_87099 -> Prop)).
Proof. exact (eq_refl (@ex (_87099 -> Prop))). Qed.
Lemma lem3344187 {_87099 : Type'} (t : type686 _87099) (x : _87099) : (term40 _87099 t x) = (term40 _87099 t x).
Proof. exact (MK_COMB (@lem3344186 _87099) (@lem3344185 _87099 t x)). Qed.
Lemma lem3344192 {_87099 : Type'} (s : type686 _87099) (t : _87099 -> Prop) (x : _87099) : (term37 _87099 s t x) = (term37 _87099 s t x).
Proof. exact (eq_refl (term37 _87099 s t x)). Qed.
Lemma lem3344193 {_87099 : Type'} (s : type686 _87099) (x : _87099) : (term39 _87099 s x) = (term39 _87099 s x).
Proof. exact (fun_ext (fun t : _87099 -> Prop => @lem3344192 _87099 s t x)). Qed.
Lemma lem3344194 {_87099 : Type'} : (@ex (_87099 -> Prop)) = (@ex (_87099 -> Prop)).
Proof. exact (eq_refl (@ex (_87099 -> Prop))). Qed.
Lemma lem3344195 {_87099 : Type'} (s : type686 _87099) (x : _87099) : (term40 _87099 s x) = (term40 _87099 s x).
Proof. exact (MK_COMB (@lem3344194 _87099) (@lem3344193 _87099 s x)). Qed.
Lemma lem3344196 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3344197 {_87099 : Type'} (s : type686 _87099) (x : _87099) : (term42 _87099 s x) = (term42 _87099 s x).
Proof. exact (MK_COMB (@lem3344196) (@lem3344195 _87099 s x)). Qed.
Lemma lem3344198 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term43 _87099 s t x) = (term43 _87099 s t x).
Proof. exact (MK_COMB (@lem3344197 _87099 s x) (@lem3344187 _87099 t x)). Qed.
Lemma lem3344207 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term26 _87099 s t t' x) = (term26 _87099 s t t' x).
Proof. exact (eq_refl (term26 _87099 s t t' x)). Qed.
Lemma lem3344208 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term28 _87099 s t x) = (term28 _87099 s t x).
Proof. exact (fun_ext (fun t' : _87099 -> Prop => @lem3344207 _87099 s t t' x)). Qed.
Lemma lem3344209 {_87099 : Type'} : (@ex (_87099 -> Prop)) = (@ex (_87099 -> Prop)).
Proof. exact (eq_refl (@ex (_87099 -> Prop))). Qed.
Lemma lem3344210 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term29 _87099 s t x) = (term29 _87099 s t x).
Proof. exact (MK_COMB (@lem3344209 _87099) (@lem3344208 _87099 s t x)). Qed.
Lemma lem3344211 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3344212 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term31 _87099 s t x) = (term31 _87099 s t x).
Proof. exact (MK_COMB (@lem3344211) (@lem3344210 _87099 s t x)). Qed.
Lemma lem3344213 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : ((term29 _87099 s t x) = (term43 _87099 s t x)) = ((term29 _87099 s t x) = (term43 _87099 s t x)).
Proof. exact (MK_COMB (@lem3344212 _87099 s t x) (@lem3344198 _87099 s t x)). Qed.
Lemma lem3344214 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) : (term45 _87099 s t) = (term45 _87099 s t).
Proof. exact (fun_ext (fun x : _87099 => @lem3344213 _87099 s t x)). Qed.
Lemma lem3344215 {_87099 : Type'} : (@all _87099) = (@all _87099).
Proof. exact (eq_refl (@all _87099)). Qed.
Lemma lem3344216 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) : (term46 _87099 s t) = (term46 _87099 s t).
Proof. exact (MK_COMB (@lem3344215 _87099) (@lem3344214 _87099 s t)). Qed.
Lemma lem3344217 {_87099 : Type'} (s : type686 _87099) : (term47 _87099 s) = (term47 _87099 s).
Proof. exact (fun_ext (fun t : type686 _87099 => @lem3344216 _87099 s t)). Qed.
Lemma lem3344218 {_87099 : Type'} : (@all ((_87099 -> Prop) -> Prop)) = (@all ((_87099 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87099 -> Prop) -> Prop))). Qed.
Lemma lem3344219 {_87099 : Type'} (s : type686 _87099) : (term48 _87099 s) = (term48 _87099 s).
Proof. exact (MK_COMB (@lem3344218 _87099) (@lem3344217 _87099 s)). Qed.
Lemma lem3344220 {_87099 : Type'} : (term49 _87099) = (term49 _87099).
Proof. exact (fun_ext (fun s : type686 _87099 => @lem3344219 _87099 s)). Qed.
Lemma lem3344221 {_87099 : Type'} : (@all ((_87099 -> Prop) -> Prop)) = (@all ((_87099 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87099 -> Prop) -> Prop))). Qed.
Lemma lem3344222 {_87099 : Type'} : (term50 _87099) = (term50 _87099).
Proof. exact (MK_COMB (@lem3344221 _87099) (@lem3344220 _87099)). Qed.
Lemma lem3344271 {_87099 : Type'} : (term52 _87099) = (term50 _87099).
Proof. exact (TRANS (@lem3344179 _87099) (@lem3344222 _87099)). Qed.
Lemma lem3344272 {_87099 : Type'} : (term50 _87099) = (term52 _87099).
Proof. exact (SYM (@lem3344271 _87099)). Qed.
Lemma lem3344274 (p : Prop) : p = (term51 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3344275 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : ((term29 _87099 s t x) = (term43 _87099 s t x)) = (term59 _87099 s t x).
Proof. exact (@lem3344274 ((term29 _87099 s t x) = (term43 _87099 s t x))). Qed.
Lemma lem3344276 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term59 _87099 s t x) = ((term29 _87099 s t x) = (term43 _87099 s t x)).
Proof. exact (SYM (@lem3344275 _87099 s t x)). Qed.
Lemma lem3344277 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term60 _87099 s t x) : term60 _87099 s t x.
Proof. exact (h1). Qed.
Lemma lem3344286 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) : (term61 _87099 s t t') = (term62 _87099 s t t').
Proof. exact (@lem17160 (s t') (t t')). Qed.
Lemma lem3344290 {_87099 : Type'} (t : _87099 -> Prop) (x : _87099) : (term63 _87099 t x) = (term63 _87099 t x).
Proof. exact (eq_refl (term63 _87099 t x)). Qed.
Lemma lem3344292 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3344293 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) : (term64 _87099 s t t') = (term65 _87099 s t t').
Proof. exact (MK_COMB (@lem3344292) (@lem3344286 _87099 s t t')). Qed.
Lemma lem3344294 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term66 _87099 s t t' x) = (term67 _87099 s t t' x).
Proof. exact (MK_COMB (@lem3344293 _87099 s t t') (@lem3344290 _87099 t' x)). Qed.
Lemma lem3344295 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term68 _87099 s t t' x) = (term66 _87099 s t t' x).
Proof. exact (@lem17045 (term22 _87099 s t t') (t' x)). Qed.
Lemma lem3344296 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term68 _87099 s t t' x) = (term67 _87099 s t t' x).
Proof. exact (TRANS (@lem3344295 _87099 s t t' x) (@lem3344294 _87099 s t t' x)). Qed.
Lemma lem3344299 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term26 _87099 s t t' x) = (term26 _87099 s t t' x).
Proof. exact (eq_refl (term26 _87099 s t t' x)). Qed.
Lemma lem3344300 {_87099 : Type'} (P : type686 _87099) : (term69 _87099 P) = (term70 _87099 P).
Proof. exact (@lem18394 (_87099 -> Prop) P). Qed.
Lemma lem3344301 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term71 _87099 s t x) = (term72 _87099 s t x).
Proof. exact (@lem3344300 _87099 (term28 _87099 s t x)). Qed.
Lemma lem3344302 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term73 _87099 s t x t') = (term26 _87099 s t t' x).
Proof. exact (eq_refl (term73 _87099 s t x t')). Qed.
Lemma lem3344303 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3344304 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term74 _87099 s t x t') = (term68 _87099 s t t' x).
Proof. exact (MK_COMB (@lem3344303) (@lem3344302 _87099 s t t' x)). Qed.
Lemma lem3344305 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term74 _87099 s t x t') = (term67 _87099 s t t' x).
Proof. exact (TRANS (@lem3344304 _87099 s t t' x) (@lem3344296 _87099 s t t' x)). Qed.
Lemma lem3344306 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term75 _87099 s t x) = (term76 _87099 s t x).
Proof. exact (fun_ext (fun t' : _87099 -> Prop => @lem3344305 _87099 s t t' x)). Qed.
Lemma lem3344307 {_87099 : Type'} : (@all (_87099 -> Prop)) = (@all (_87099 -> Prop)).
Proof. exact (eq_refl (@all (_87099 -> Prop))). Qed.
Lemma lem3344308 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term72 _87099 s t x) = (term77 _87099 s t x).
Proof. exact (MK_COMB (@lem3344307 _87099) (@lem3344306 _87099 s t x)). Qed.
Lemma lem3344309 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term71 _87099 s t x) = (term77 _87099 s t x).
Proof. exact (TRANS (@lem3344301 _87099 s t x) (@lem3344308 _87099 s t x)). Qed.
Lemma lem3344310 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term28 _87099 s t x) = (term28 _87099 s t x).
Proof. exact (fun_ext (fun t' : _87099 -> Prop => @lem3344299 _87099 s t t' x)). Qed.
Lemma lem3344311 {_87099 : Type'} : (@ex (_87099 -> Prop)) = (@ex (_87099 -> Prop)).
Proof. exact (eq_refl (@ex (_87099 -> Prop))). Qed.
Lemma lem3344312 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term29 _87099 s t x) = (term29 _87099 s t x).
Proof. exact (MK_COMB (@lem3344311 _87099) (@lem3344310 _87099 s t x)). Qed.
Lemma lem3344321 {_87099 : Type'} (s : type686 _87099) (t : _87099 -> Prop) (x : _87099) : (term78 _87099 s t x) = (term79 _87099 s t x).
Proof. exact (@lem17045 (s t) (t x)). Qed.
Lemma lem3344324 {_87099 : Type'} (s : type686 _87099) (t : _87099 -> Prop) (x : _87099) : (term37 _87099 s t x) = (term37 _87099 s t x).
Proof. exact (eq_refl (term37 _87099 s t x)). Qed.
Lemma lem3344325 {_87099 : Type'} (P : type686 _87099) : (term69 _87099 P) = (term70 _87099 P).
Proof. exact (@lem18394 (_87099 -> Prop) P). Qed.
Lemma lem3344326 {_87099 : Type'} (s : type686 _87099) (x : _87099) : (term80 _87099 s x) = (term81 _87099 s x).
Proof. exact (@lem3344325 _87099 (term39 _87099 s x)). Qed.
Lemma lem3344327 {_87099 : Type'} (s : type686 _87099) (t : _87099 -> Prop) (x : _87099) : (term82 _87099 s x t) = (term37 _87099 s t x).
Proof. exact (eq_refl (term82 _87099 s x t)). Qed.
Lemma lem3344328 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3344329 {_87099 : Type'} (s : type686 _87099) (t : _87099 -> Prop) (x : _87099) : (term83 _87099 s x t) = (term78 _87099 s t x).
Proof. exact (MK_COMB (@lem3344328) (@lem3344327 _87099 s t x)). Qed.
Lemma lem3344330 {_87099 : Type'} (s : type686 _87099) (t : _87099 -> Prop) (x : _87099) : (term83 _87099 s x t) = (term79 _87099 s t x).
Proof. exact (TRANS (@lem3344329 _87099 s t x) (@lem3344321 _87099 s t x)). Qed.
Lemma lem3344331 {_87099 : Type'} (s : type686 _87099) (x : _87099) : (term84 _87099 s x) = (term85 _87099 s x).
Proof. exact (fun_ext (fun t : _87099 -> Prop => @lem3344330 _87099 s t x)). Qed.
Lemma lem3344332 {_87099 : Type'} : (@all (_87099 -> Prop)) = (@all (_87099 -> Prop)).
Proof. exact (eq_refl (@all (_87099 -> Prop))). Qed.
Lemma lem3344333 {_87099 : Type'} (s : type686 _87099) (x : _87099) : (term81 _87099 s x) = (term86 _87099 s x).
Proof. exact (MK_COMB (@lem3344332 _87099) (@lem3344331 _87099 s x)). Qed.
Lemma lem3344334 {_87099 : Type'} (s : type686 _87099) (x : _87099) : (term80 _87099 s x) = (term86 _87099 s x).
Proof. exact (TRANS (@lem3344326 _87099 s x) (@lem3344333 _87099 s x)). Qed.
Lemma lem3344335 {_87099 : Type'} (s : type686 _87099) (x : _87099) : (term39 _87099 s x) = (term39 _87099 s x).
Proof. exact (fun_ext (fun t : _87099 -> Prop => @lem3344324 _87099 s t x)). Qed.
Lemma lem3344336 {_87099 : Type'} : (@ex (_87099 -> Prop)) = (@ex (_87099 -> Prop)).
Proof. exact (eq_refl (@ex (_87099 -> Prop))). Qed.
Lemma lem3344337 {_87099 : Type'} (s : type686 _87099) (x : _87099) : (term40 _87099 s x) = (term40 _87099 s x).
Proof. exact (MK_COMB (@lem3344336 _87099) (@lem3344335 _87099 s x)). Qed.
Lemma lem3344346 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term78 _87099 t t' x) = (term79 _87099 t t' x).
Proof. exact (@lem17045 (t t') (t' x)). Qed.
Lemma lem3344349 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term37 _87099 t t' x) = (term37 _87099 t t' x).
Proof. exact (eq_refl (term37 _87099 t t' x)). Qed.
Lemma lem3344350 {_87099 : Type'} (P : type686 _87099) : (term69 _87099 P) = (term70 _87099 P).
Proof. exact (@lem18394 (_87099 -> Prop) P). Qed.
Lemma lem3344351 {_87099 : Type'} (t : type686 _87099) (x : _87099) : (term80 _87099 t x) = (term81 _87099 t x).
Proof. exact (@lem3344350 _87099 (term39 _87099 t x)). Qed.
Lemma lem3344352 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term82 _87099 t x t') = (term37 _87099 t t' x).
Proof. exact (eq_refl (term82 _87099 t x t')). Qed.
Lemma lem3344353 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3344354 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term83 _87099 t x t') = (term78 _87099 t t' x).
Proof. exact (MK_COMB (@lem3344353) (@lem3344352 _87099 t t' x)). Qed.
Lemma lem3344355 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term83 _87099 t x t') = (term79 _87099 t t' x).
Proof. exact (TRANS (@lem3344354 _87099 t t' x) (@lem3344346 _87099 t t' x)). Qed.
Lemma lem3344356 {_87099 : Type'} (t : type686 _87099) (x : _87099) : (term84 _87099 t x) = (term85 _87099 t x).
Proof. exact (fun_ext (fun t' : _87099 -> Prop => @lem3344355 _87099 t t' x)). Qed.
Lemma lem3344357 {_87099 : Type'} : (@all (_87099 -> Prop)) = (@all (_87099 -> Prop)).
Proof. exact (eq_refl (@all (_87099 -> Prop))). Qed.
Lemma lem3344358 {_87099 : Type'} (t : type686 _87099) (x : _87099) : (term81 _87099 t x) = (term86 _87099 t x).
Proof. exact (MK_COMB (@lem3344357 _87099) (@lem3344356 _87099 t x)). Qed.
Lemma lem3344359 {_87099 : Type'} (t : type686 _87099) (x : _87099) : (term80 _87099 t x) = (term86 _87099 t x).
Proof. exact (TRANS (@lem3344351 _87099 t x) (@lem3344358 _87099 t x)). Qed.
Lemma lem3344360 {_87099 : Type'} (t : type686 _87099) (x : _87099) : (term39 _87099 t x) = (term39 _87099 t x).
Proof. exact (fun_ext (fun t' : _87099 -> Prop => @lem3344349 _87099 t t' x)). Qed.
Lemma lem3344361 {_87099 : Type'} : (@ex (_87099 -> Prop)) = (@ex (_87099 -> Prop)).
Proof. exact (eq_refl (@ex (_87099 -> Prop))). Qed.
Lemma lem3344362 {_87099 : Type'} (t : type686 _87099) (x : _87099) : (term40 _87099 t x) = (term40 _87099 t x).
Proof. exact (MK_COMB (@lem3344361 _87099) (@lem3344360 _87099 t x)). Qed.
Lemma lem3344363 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3344364 {_87099 : Type'} (s : type686 _87099) (x : _87099) : (term87 _87099 s x) = (term88 _87099 s x).
Proof. exact (MK_COMB (@lem3344363) (@lem3344334 _87099 s x)). Qed.
Lemma lem3344365 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term89 _87099 s t x) = (term90 _87099 s t x).
Proof. exact (MK_COMB (@lem3344364 _87099 s x) (@lem3344359 _87099 t x)). Qed.
Lemma lem3344366 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term91 _87099 s t x) = (term89 _87099 s t x).
Proof. exact (@lem17160 (term40 _87099 s x) (term40 _87099 t x)). Qed.
Lemma lem3344367 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term91 _87099 s t x) = (term90 _87099 s t x).
Proof. exact (TRANS (@lem3344366 _87099 s t x) (@lem3344365 _87099 s t x)). Qed.
Lemma lem3344368 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3344369 {_87099 : Type'} (s : type686 _87099) (x : _87099) : (term42 _87099 s x) = (term42 _87099 s x).
Proof. exact (MK_COMB (@lem3344368) (@lem3344337 _87099 s x)). Qed.
Lemma lem3344370 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term43 _87099 s t x) = (term43 _87099 s t x).
Proof. exact (MK_COMB (@lem3344369 _87099 s x) (@lem3344362 _87099 t x)). Qed.
Lemma lem3344371 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3344372 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term92 _87099 s t x) = (term93 _87099 s t x).
Proof. exact (MK_COMB (@lem3344371) (@lem3344309 _87099 s t x)). Qed.
Lemma lem3344373 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term94 _87099 s t x) = (term95 _87099 s t x).
Proof. exact (MK_COMB (@lem3344372 _87099 s t x) (@lem3344370 _87099 s t x)). Qed.
Lemma lem3344374 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3344375 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term96 _87099 s t x) = (term96 _87099 s t x).
Proof. exact (MK_COMB (@lem3344374) (@lem3344312 _87099 s t x)). Qed.
Lemma lem3344376 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term97 _87099 s t x) = (term98 _87099 s t x).
Proof. exact (MK_COMB (@lem3344375 _87099 s t x) (@lem3344367 _87099 s t x)). Qed.
Lemma lem3344377 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3344378 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term99 _87099 s t x) = (term100 _87099 s t x).
Proof. exact (MK_COMB (@lem3344377) (@lem3344376 _87099 s t x)). Qed.
Lemma lem3344379 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term101 _87099 s t x) = (term102 _87099 s t x).
Proof. exact (MK_COMB (@lem3344378 _87099 s t x) (@lem3344373 _87099 s t x)). Qed.
Lemma lem3344380 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term60 _87099 s t x) = (term101 _87099 s t x).
Proof. exact (@lem17646 (term29 _87099 s t x) (term43 _87099 s t x)). Qed.
Lemma lem3344381 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term60 _87099 s t x) = (term102 _87099 s t x).
Proof. exact (TRANS (@lem3344380 _87099 s t x) (@lem3344379 _87099 s t x)). Qed.
Lemma lem3344632 {A : Type'} (P : A -> Prop) (Q : Prop) : (term103 A P Q) = (term104 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3344633 {_87099 : Type'} (P : type686 _87099) (Q : Prop) : (term105 _87099 P Q) = (term106 _87099 P Q).
Proof. exact (@lem3344632 (_87099 -> Prop) P Q). Qed.
Lemma lem3344634 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term107 _87099 s t x) = (term108 _87099 s t x).
Proof. exact (@lem3344633 _87099 (term28 _87099 s t x) (term90 _87099 s t x)). Qed.
Lemma lem3344635 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term73 _87099 s t x t') = (term26 _87099 s t t' x).
Proof. exact (eq_refl (term73 _87099 s t x t')). Qed.
Lemma lem3344636 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term109 _87099 s t x) = (term28 _87099 s t x).
Proof. exact (fun_ext (fun t' : _87099 -> Prop => @lem3344635 _87099 s t t' x)). Qed.
Lemma lem3344637 {_87099 : Type'} : (@ex (_87099 -> Prop)) = (@ex (_87099 -> Prop)).
Proof. exact (eq_refl (@ex (_87099 -> Prop))). Qed.
Lemma lem3344638 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term110 _87099 s t x) = (term29 _87099 s t x).
Proof. exact (MK_COMB (@lem3344637 _87099) (@lem3344636 _87099 s t x)). Qed.
Lemma lem3344639 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3344640 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term111 _87099 s t x) = (term96 _87099 s t x).
Proof. exact (MK_COMB (@lem3344639) (@lem3344638 _87099 s t x)). Qed.
Lemma lem3344641 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term90 _87099 s t x) = (term90 _87099 s t x).
Proof. exact (eq_refl (term90 _87099 s t x)). Qed.
Lemma lem3344642 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term107 _87099 s t x) = (term98 _87099 s t x).
Proof. exact (MK_COMB (@lem3344640 _87099 s t x) (@lem3344641 _87099 s t x)). Qed.
Lemma lem3344643 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3344644 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term112 _87099 s t x) = (term113 _87099 s t x).
Proof. exact (MK_COMB (@lem3344643) (@lem3344642 _87099 s t x)). Qed.
Lemma lem3344645 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term73 _87099 s t x t') = (term26 _87099 s t t' x).
Proof. exact (eq_refl (term73 _87099 s t x t')). Qed.
Lemma lem3344646 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3344647 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term114 _87099 s t x t') = (term115 _87099 s t t' x).
Proof. exact (MK_COMB (@lem3344646) (@lem3344645 _87099 s t t' x)). Qed.
Lemma lem3344648 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term90 _87099 s t x) = (term90 _87099 s t x).
Proof. exact (eq_refl (term90 _87099 s t x)). Qed.
Lemma lem3344649 {_87099 : Type'} (t : _87099 -> Prop) (s : type686 _87099) (t' : type686 _87099) (x : _87099) : (term116 _87099 t s t' x) = (term117 _87099 t s t' x).
Proof. exact (MK_COMB (@lem3344647 _87099 s t' t x) (@lem3344648 _87099 s t' x)). Qed.
Lemma lem3344650 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term118 _87099 s t x) = (term119 _87099 s t x).
Proof. exact (fun_ext (fun t' : _87099 -> Prop => @lem3344649 _87099 t' s t x)). Qed.
Lemma lem3344651 {_87099 : Type'} : (@ex (_87099 -> Prop)) = (@ex (_87099 -> Prop)).
Proof. exact (eq_refl (@ex (_87099 -> Prop))). Qed.
Lemma lem3344652 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term108 _87099 s t x) = (term120 _87099 s t x).
Proof. exact (MK_COMB (@lem3344651 _87099) (@lem3344650 _87099 s t x)). Qed.
Lemma lem3344653 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : ((term107 _87099 s t x) = (term108 _87099 s t x)) = ((term98 _87099 s t x) = (term120 _87099 s t x)).
Proof. exact (MK_COMB (@lem3344644 _87099 s t x) (@lem3344652 _87099 s t x)). Qed.
Lemma lem3344654 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term98 _87099 s t x) = (term120 _87099 s t x).
Proof. exact (EQ_MP (@lem3344653 _87099 s t x) (@lem3344634 _87099 s t x)). Qed.
Lemma lem3344655 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3344656 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term100 _87099 s t x) = (term121 _87099 s t x).
Proof. exact (MK_COMB (@lem3344655) (@lem3344654 _87099 s t x)). Qed.
Lemma lem3344658 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term122 A P Q) = (term123 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3344659 {_87099 : Type'} (P : type686 _87099) (Q : type686 _87099) : (term124 _87099 P Q) = (term125 _87099 P Q).
Proof. exact (@lem3344658 (_87099 -> Prop) P Q). Qed.
Lemma lem3344660 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term126 _87099 s t x) = (term127 _87099 s t x).
Proof. exact (@lem3344659 _87099 (term39 _87099 s x) (term39 _87099 t x)). Qed.
Lemma lem3344661 {_87099 : Type'} (s : type686 _87099) (t : _87099 -> Prop) (x : _87099) : (term82 _87099 s x t) = (term37 _87099 s t x).
Proof. exact (eq_refl (term82 _87099 s x t)). Qed.
Lemma lem3344662 {_87099 : Type'} (s : type686 _87099) (x : _87099) : (term128 _87099 s x) = (term39 _87099 s x).
Proof. exact (fun_ext (fun t : _87099 -> Prop => @lem3344661 _87099 s t x)). Qed.
Lemma lem3344663 {_87099 : Type'} : (@ex (_87099 -> Prop)) = (@ex (_87099 -> Prop)).
Proof. exact (eq_refl (@ex (_87099 -> Prop))). Qed.
Lemma lem3344664 {_87099 : Type'} (s : type686 _87099) (x : _87099) : (term129 _87099 s x) = (term40 _87099 s x).
Proof. exact (MK_COMB (@lem3344663 _87099) (@lem3344662 _87099 s x)). Qed.
Lemma lem3344665 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3344666 {_87099 : Type'} (s : type686 _87099) (x : _87099) : (term130 _87099 s x) = (term42 _87099 s x).
Proof. exact (MK_COMB (@lem3344665) (@lem3344664 _87099 s x)). Qed.
Lemma lem3344667 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term82 _87099 t x t') = (term37 _87099 t t' x).
Proof. exact (eq_refl (term82 _87099 t x t')). Qed.
Lemma lem3344668 {_87099 : Type'} (t : type686 _87099) (x : _87099) : (term128 _87099 t x) = (term39 _87099 t x).
Proof. exact (fun_ext (fun t' : _87099 -> Prop => @lem3344667 _87099 t t' x)). Qed.
Lemma lem3344669 {_87099 : Type'} : (@ex (_87099 -> Prop)) = (@ex (_87099 -> Prop)).
Proof. exact (eq_refl (@ex (_87099 -> Prop))). Qed.
Lemma lem3344670 {_87099 : Type'} (t : type686 _87099) (x : _87099) : (term129 _87099 t x) = (term40 _87099 t x).
Proof. exact (MK_COMB (@lem3344669 _87099) (@lem3344668 _87099 t x)). Qed.
Lemma lem3344671 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term126 _87099 s t x) = (term43 _87099 s t x).
Proof. exact (MK_COMB (@lem3344666 _87099 s x) (@lem3344670 _87099 t x)). Qed.
Lemma lem3344672 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3344673 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term131 _87099 s t x) = (term132 _87099 s t x).
Proof. exact (MK_COMB (@lem3344672) (@lem3344671 _87099 s t x)). Qed.
Lemma lem3344674 {_87099 : Type'} (s : type686 _87099) (t : _87099 -> Prop) (x : _87099) : (term82 _87099 s x t) = (term37 _87099 s t x).
Proof. exact (eq_refl (term82 _87099 s x t)). Qed.
Lemma lem3344675 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3344676 {_87099 : Type'} (s : type686 _87099) (t : _87099 -> Prop) (x : _87099) : (term133 _87099 s x t) = (term134 _87099 s t x).
Proof. exact (MK_COMB (@lem3344675) (@lem3344674 _87099 s t x)). Qed.
Lemma lem3344677 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term82 _87099 t x t') = (term37 _87099 t t' x).
Proof. exact (eq_refl (term82 _87099 t x t')). Qed.
Lemma lem3344678 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term135 _87099 s t x t') = (term136 _87099 s t t' x).
Proof. exact (MK_COMB (@lem3344676 _87099 s t' x) (@lem3344677 _87099 t t' x)). Qed.
Lemma lem3344679 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term137 _87099 s t x) = (term138 _87099 s t x).
Proof. exact (fun_ext (fun t' : _87099 -> Prop => @lem3344678 _87099 s t t' x)). Qed.
Lemma lem3344680 {_87099 : Type'} : (@ex (_87099 -> Prop)) = (@ex (_87099 -> Prop)).
Proof. exact (eq_refl (@ex (_87099 -> Prop))). Qed.
Lemma lem3344681 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term127 _87099 s t x) = (term139 _87099 s t x).
Proof. exact (MK_COMB (@lem3344680 _87099) (@lem3344679 _87099 s t x)). Qed.
Lemma lem3344682 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : ((term126 _87099 s t x) = (term127 _87099 s t x)) = ((term43 _87099 s t x) = (term139 _87099 s t x)).
Proof. exact (MK_COMB (@lem3344673 _87099 s t x) (@lem3344681 _87099 s t x)). Qed.
Lemma lem3344683 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term43 _87099 s t x) = (term139 _87099 s t x).
Proof. exact (EQ_MP (@lem3344682 _87099 s t x) (@lem3344660 _87099 s t x)). Qed.
Lemma lem3344684 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term93 _87099 s t x) = (term93 _87099 s t x).
Proof. exact (eq_refl (term93 _87099 s t x)). Qed.
Lemma lem3344685 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term95 _87099 s t x) = (term140 _87099 s t x).
Proof. exact (MK_COMB (@lem3344684 _87099 s t x) (@lem3344683 _87099 s t x)). Qed.
Lemma lem3344687 {A : Type'} (P : Prop) (Q : A -> Prop) : (term141 A P Q) = (term142 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3344688 {_87099 : Type'} (P : Prop) (Q : type686 _87099) : (term143 _87099 P Q) = (term144 _87099 P Q).
Proof. exact (@lem3344687 (_87099 -> Prop) P Q). Qed.
Lemma lem3344689 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term145 _87099 s t x) = (term146 _87099 s t x).
Proof. exact (@lem3344688 _87099 (term77 _87099 s t x) (term138 _87099 s t x)). Qed.
Lemma lem3344690 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term147 _87099 s t x t') = (term136 _87099 s t t' x).
Proof. exact (eq_refl (term147 _87099 s t x t')). Qed.
Lemma lem3344691 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term148 _87099 s t x) = (term138 _87099 s t x).
Proof. exact (fun_ext (fun t' : _87099 -> Prop => @lem3344690 _87099 s t t' x)). Qed.
Lemma lem3344692 {_87099 : Type'} : (@ex (_87099 -> Prop)) = (@ex (_87099 -> Prop)).
Proof. exact (eq_refl (@ex (_87099 -> Prop))). Qed.
Lemma lem3344693 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term149 _87099 s t x) = (term139 _87099 s t x).
Proof. exact (MK_COMB (@lem3344692 _87099) (@lem3344691 _87099 s t x)). Qed.
Lemma lem3344694 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term93 _87099 s t x) = (term93 _87099 s t x).
Proof. exact (eq_refl (term93 _87099 s t x)). Qed.
Lemma lem3344695 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term145 _87099 s t x) = (term140 _87099 s t x).
Proof. exact (MK_COMB (@lem3344694 _87099 s t x) (@lem3344693 _87099 s t x)). Qed.
Lemma lem3344696 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3344697 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term150 _87099 s t x) = (term151 _87099 s t x).
Proof. exact (MK_COMB (@lem3344696) (@lem3344695 _87099 s t x)). Qed.
Lemma lem3344698 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term147 _87099 s t x t') = (term136 _87099 s t t' x).
Proof. exact (eq_refl (term147 _87099 s t x t')). Qed.
Lemma lem3344699 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term93 _87099 s t x) = (term93 _87099 s t x).
Proof. exact (eq_refl (term93 _87099 s t x)). Qed.
Lemma lem3344700 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term152 _87099 s t x t') = (term153 _87099 s t t' x).
Proof. exact (MK_COMB (@lem3344699 _87099 s t x) (@lem3344698 _87099 s t t' x)). Qed.
Lemma lem3344701 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term154 _87099 s t x) = (term155 _87099 s t x).
Proof. exact (fun_ext (fun t' : _87099 -> Prop => @lem3344700 _87099 s t t' x)). Qed.
Lemma lem3344702 {_87099 : Type'} : (@ex (_87099 -> Prop)) = (@ex (_87099 -> Prop)).
Proof. exact (eq_refl (@ex (_87099 -> Prop))). Qed.
Lemma lem3344703 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term146 _87099 s t x) = (term156 _87099 s t x).
Proof. exact (MK_COMB (@lem3344702 _87099) (@lem3344701 _87099 s t x)). Qed.
Lemma lem3344704 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : ((term145 _87099 s t x) = (term146 _87099 s t x)) = ((term140 _87099 s t x) = (term156 _87099 s t x)).
Proof. exact (MK_COMB (@lem3344697 _87099 s t x) (@lem3344703 _87099 s t x)). Qed.
Lemma lem3344705 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term140 _87099 s t x) = (term156 _87099 s t x).
Proof. exact (EQ_MP (@lem3344704 _87099 s t x) (@lem3344689 _87099 s t x)). Qed.
Lemma lem3344706 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term95 _87099 s t x) = (term156 _87099 s t x).
Proof. exact (TRANS (@lem3344685 _87099 s t x) (@lem3344705 _87099 s t x)). Qed.
Lemma lem3344707 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term102 _87099 s t x) = (term157 _87099 s t x).
Proof. exact (MK_COMB (@lem3344656 _87099 s t x) (@lem3344706 _87099 s t x)). Qed.
Lemma lem3344709 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term122 A P Q) = (term123 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3344710 {_87099 : Type'} (P : type686 _87099) (Q : type686 _87099) : (term124 _87099 P Q) = (term125 _87099 P Q).
Proof. exact (@lem3344709 (_87099 -> Prop) P Q). Qed.
Lemma lem3344711 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term158 _87099 s t x) = (term159 _87099 s t x).
Proof. exact (@lem3344710 _87099 (term119 _87099 s t x) (term155 _87099 s t x)). Qed.
Lemma lem3344712 {_87099 : Type'} (t : _87099 -> Prop) (s : type686 _87099) (t' : type686 _87099) (x : _87099) : (term160 _87099 s t' x t) = (term117 _87099 t s t' x).
Proof. exact (eq_refl (term160 _87099 s t' x t)). Qed.
Lemma lem3344713 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term161 _87099 s t x) = (term119 _87099 s t x).
Proof. exact (fun_ext (fun t' : _87099 -> Prop => @lem3344712 _87099 t' s t x)). Qed.
Lemma lem3344714 {_87099 : Type'} : (@ex (_87099 -> Prop)) = (@ex (_87099 -> Prop)).
Proof. exact (eq_refl (@ex (_87099 -> Prop))). Qed.
Lemma lem3344715 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term162 _87099 s t x) = (term120 _87099 s t x).
Proof. exact (MK_COMB (@lem3344714 _87099) (@lem3344713 _87099 s t x)). Qed.
Lemma lem3344716 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3344717 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term163 _87099 s t x) = (term121 _87099 s t x).
Proof. exact (MK_COMB (@lem3344716) (@lem3344715 _87099 s t x)). Qed.
Lemma lem3344718 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term164 _87099 s t x t') = (term153 _87099 s t t' x).
Proof. exact (eq_refl (term164 _87099 s t x t')). Qed.
Lemma lem3344719 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term165 _87099 s t x) = (term155 _87099 s t x).
Proof. exact (fun_ext (fun t' : _87099 -> Prop => @lem3344718 _87099 s t t' x)). Qed.
Lemma lem3344720 {_87099 : Type'} : (@ex (_87099 -> Prop)) = (@ex (_87099 -> Prop)).
Proof. exact (eq_refl (@ex (_87099 -> Prop))). Qed.
Lemma lem3344721 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term166 _87099 s t x) = (term156 _87099 s t x).
Proof. exact (MK_COMB (@lem3344720 _87099) (@lem3344719 _87099 s t x)). Qed.
Lemma lem3344722 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term158 _87099 s t x) = (term157 _87099 s t x).
Proof. exact (MK_COMB (@lem3344717 _87099 s t x) (@lem3344721 _87099 s t x)). Qed.
Lemma lem3344723 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3344724 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term167 _87099 s t x) = (term168 _87099 s t x).
Proof. exact (MK_COMB (@lem3344723) (@lem3344722 _87099 s t x)). Qed.
Lemma lem3344725 {_87099 : Type'} (t : _87099 -> Prop) (s : type686 _87099) (t' : type686 _87099) (x : _87099) : (term160 _87099 s t' x t) = (term117 _87099 t s t' x).
Proof. exact (eq_refl (term160 _87099 s t' x t)). Qed.
Lemma lem3344726 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3344727 {_87099 : Type'} (t : _87099 -> Prop) (s : type686 _87099) (t' : type686 _87099) (x : _87099) : (term169 _87099 s t' x t) = (term170 _87099 t s t' x).
Proof. exact (MK_COMB (@lem3344726) (@lem3344725 _87099 t s t' x)). Qed.
Lemma lem3344728 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term164 _87099 s t x t') = (term153 _87099 s t t' x).
Proof. exact (eq_refl (term164 _87099 s t x t')). Qed.
Lemma lem3344729 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term171 _87099 s t x t') = (term172 _87099 s t t' x).
Proof. exact (MK_COMB (@lem3344727 _87099 t' s t x) (@lem3344728 _87099 s t t' x)). Qed.
Lemma lem3344730 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term173 _87099 s t x) = (term174 _87099 s t x).
Proof. exact (fun_ext (fun t' : _87099 -> Prop => @lem3344729 _87099 s t t' x)). Qed.
Lemma lem3344731 {_87099 : Type'} : (@ex (_87099 -> Prop)) = (@ex (_87099 -> Prop)).
Proof. exact (eq_refl (@ex (_87099 -> Prop))). Qed.
Lemma lem3344732 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term159 _87099 s t x) = (term175 _87099 s t x).
Proof. exact (MK_COMB (@lem3344731 _87099) (@lem3344730 _87099 s t x)). Qed.
Lemma lem3344733 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : ((term158 _87099 s t x) = (term159 _87099 s t x)) = ((term157 _87099 s t x) = (term175 _87099 s t x)).
Proof. exact (MK_COMB (@lem3344724 _87099 s t x) (@lem3344732 _87099 s t x)). Qed.
Lemma lem3344734 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term157 _87099 s t x) = (term175 _87099 s t x).
Proof. exact (EQ_MP (@lem3344733 _87099 s t x) (@lem3344711 _87099 s t x)). Qed.
Lemma lem3344736 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term102 _87099 s t x) = (term175 _87099 s t x).
Proof. exact (TRANS (@lem3344707 _87099 s t x) (@lem3344734 _87099 s t x)). Qed.
Lemma lem3344737 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term60 _87099 s t x) = (term175 _87099 s t x).
Proof. exact (TRANS (@lem3344381 _87099 s t x) (@lem3344736 _87099 s t x)). Qed.
Lemma lem3344738 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term60 _87099 s t x) : term175 _87099 s t x.
Proof. exact (EQ_MP (@lem3344737 _87099 s t x) (@lem3344277 _87099 s t x h1)). Qed.
Lemma lem3344739 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term172 _87099 s t t' x) : term172 _87099 s t t' x.
Proof. exact (h1). Qed.
Lemma lem3344744 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3344745 {_87099 : Type'} (f : _87099 -> Prop) (x : _87099) : (f x) = (@I (_87099 -> Prop) f x).
Proof. exact (@lem3344744 _87099 Prop f x). Qed.
Lemma lem3344747 {_87099 : Type'} (t' : _87099 -> Prop) (x : _87099) : (t' x) = (@I (_87099 -> Prop) t' x).
Proof. exact (@lem3344745 _87099 t' x). Qed.
Lemma lem3344752 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3344753 {_87099 : Type'} (f : type686 _87099) (x : _87099 -> Prop) : (f x) = (@I ((_87099 -> Prop) -> Prop) f x).
Proof. exact (@lem3344752 (_87099 -> Prop) Prop f x). Qed.
Lemma lem3344755 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) : (t t') = (@I ((_87099 -> Prop) -> Prop) t t').
Proof. exact (@lem3344753 _87099 t t'). Qed.
Lemma lem3344756 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3344757 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) : (term35 _87099 t t') = (term176 _87099 t t').
Proof. exact (MK_COMB (@lem3344756) (@lem3344755 _87099 t t')). Qed.
Lemma lem3344758 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term37 _87099 t t' x) = (term177 _87099 t t' x).
Proof. exact (MK_COMB (@lem3344757 _87099 t t') (@lem3344747 _87099 t' x)). Qed.
Lemma lem3344763 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3344764 {_87099 : Type'} (f : _87099 -> Prop) (x : _87099) : (f x) = (@I (_87099 -> Prop) f x).
Proof. exact (@lem3344763 _87099 Prop f x). Qed.
Lemma lem3344766 {_87099 : Type'} (t' : _87099 -> Prop) (x : _87099) : (t' x) = (@I (_87099 -> Prop) t' x).
Proof. exact (@lem3344764 _87099 t' x). Qed.
Lemma lem3344771 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3344772 {_87099 : Type'} (f : type686 _87099) (x : _87099 -> Prop) : (f x) = (@I ((_87099 -> Prop) -> Prop) f x).
Proof. exact (@lem3344771 (_87099 -> Prop) Prop f x). Qed.
Lemma lem3344774 {_87099 : Type'} (s : type686 _87099) (t' : _87099 -> Prop) : (s t') = (@I ((_87099 -> Prop) -> Prop) s t').
Proof. exact (@lem3344772 _87099 s t'). Qed.
Lemma lem3344775 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3344776 {_87099 : Type'} (s : type686 _87099) (t' : _87099 -> Prop) : (term35 _87099 s t') = (term176 _87099 s t').
Proof. exact (MK_COMB (@lem3344775) (@lem3344774 _87099 s t')). Qed.
Lemma lem3344777 {_87099 : Type'} (s : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term37 _87099 s t' x) = (term177 _87099 s t' x).
Proof. exact (MK_COMB (@lem3344776 _87099 s t') (@lem3344766 _87099 t' x)). Qed.
Lemma lem3344778 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3344779 {_87099 : Type'} (s : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term134 _87099 s t' x) = (term178 _87099 s t' x).
Proof. exact (MK_COMB (@lem3344778) (@lem3344777 _87099 s t' x)). Qed.
Lemma lem3344780 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term136 _87099 s t t' x) = (term179 _87099 s t t' x).
Proof. exact (MK_COMB (@lem3344779 _87099 s t' x) (@lem3344758 _87099 t t' x)). Qed.
Lemma lem3344781 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3344786 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3344787 {_87099 : Type'} (f : _87099 -> Prop) (x : _87099) : (f x) = (@I (_87099 -> Prop) f x).
Proof. exact (@lem3344786 _87099 Prop f x). Qed.
Lemma lem3344789 {_87099 : Type'} (t : _87099 -> Prop) (x : _87099) : (t x) = (@I (_87099 -> Prop) t x).
Proof. exact (@lem3344787 _87099 t x). Qed.
Lemma lem3344790 {_87099 : Type'} (t : _87099 -> Prop) (x : _87099) : (term63 _87099 t x) = (term180 _87099 t x).
Proof. exact (MK_COMB (@lem3344781) (@lem3344789 _87099 t x)). Qed.
Lemma lem3344791 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3344796 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3344797 {_87099 : Type'} (f : type686 _87099) (x : _87099 -> Prop) : (f x) = (@I ((_87099 -> Prop) -> Prop) f x).
Proof. exact (@lem3344796 (_87099 -> Prop) Prop f x). Qed.
Lemma lem3344799 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) : (t t') = (@I ((_87099 -> Prop) -> Prop) t t').
Proof. exact (@lem3344797 _87099 t t'). Qed.
Lemma lem3344800 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) : (term181 _87099 t t') = (term182 _87099 t t').
Proof. exact (MK_COMB (@lem3344791) (@lem3344799 _87099 t t')). Qed.
Lemma lem3344801 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3344806 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3344807 {_87099 : Type'} (f : type686 _87099) (x : _87099 -> Prop) : (f x) = (@I ((_87099 -> Prop) -> Prop) f x).
Proof. exact (@lem3344806 (_87099 -> Prop) Prop f x). Qed.
Lemma lem3344809 {_87099 : Type'} (s : type686 _87099) (t : _87099 -> Prop) : (s t) = (@I ((_87099 -> Prop) -> Prop) s t).
Proof. exact (@lem3344807 _87099 s t). Qed.
Lemma lem3344810 {_87099 : Type'} (s : type686 _87099) (t : _87099 -> Prop) : (term181 _87099 s t) = (term182 _87099 s t).
Proof. exact (MK_COMB (@lem3344801) (@lem3344809 _87099 s t)). Qed.
Lemma lem3344811 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3344812 {_87099 : Type'} (s : type686 _87099) (t : _87099 -> Prop) : (term183 _87099 s t) = (term184 _87099 s t).
Proof. exact (MK_COMB (@lem3344811) (@lem3344810 _87099 s t)). Qed.
Lemma lem3344813 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) : (term62 _87099 s t t') = (term185 _87099 s t t').
Proof. exact (MK_COMB (@lem3344812 _87099 s t') (@lem3344800 _87099 t t')). Qed.
Lemma lem3344814 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3344815 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) : (term65 _87099 s t t') = (term186 _87099 s t t').
Proof. exact (MK_COMB (@lem3344814) (@lem3344813 _87099 s t t')). Qed.
Lemma lem3344816 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term67 _87099 s t t' x) = (term187 _87099 s t t' x).
Proof. exact (MK_COMB (@lem3344815 _87099 s t t') (@lem3344790 _87099 t' x)). Qed.
Lemma lem3344817 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term76 _87099 s t x) = (term188 _87099 s t x).
Proof. exact (fun_ext (fun t' : _87099 -> Prop => @lem3344816 _87099 s t t' x)). Qed.
Lemma lem3344818 {_87099 : Type'} : (@all (_87099 -> Prop)) = (@all (_87099 -> Prop)).
Proof. exact (eq_refl (@all (_87099 -> Prop))). Qed.
Lemma lem3344819 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term77 _87099 s t x) = (term189 _87099 s t x).
Proof. exact (MK_COMB (@lem3344818 _87099) (@lem3344817 _87099 s t x)). Qed.
Lemma lem3344820 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3344821 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term93 _87099 s t x) = (term190 _87099 s t x).
Proof. exact (MK_COMB (@lem3344820) (@lem3344819 _87099 s t x)). Qed.
Lemma lem3344822 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term153 _87099 s t t' x) = (term191 _87099 s t t' x).
Proof. exact (MK_COMB (@lem3344821 _87099 s t x) (@lem3344780 _87099 s t t' x)). Qed.
Lemma lem3344823 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3344828 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3344829 {_87099 : Type'} (f : _87099 -> Prop) (x : _87099) : (f x) = (@I (_87099 -> Prop) f x).
Proof. exact (@lem3344828 _87099 Prop f x). Qed.
Lemma lem3344831 {_87099 : Type'} (t : _87099 -> Prop) (x : _87099) : (t x) = (@I (_87099 -> Prop) t x).
Proof. exact (@lem3344829 _87099 t x). Qed.
Lemma lem3344832 {_87099 : Type'} (t : _87099 -> Prop) (x : _87099) : (term63 _87099 t x) = (term180 _87099 t x).
Proof. exact (MK_COMB (@lem3344823) (@lem3344831 _87099 t x)). Qed.
Lemma lem3344833 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3344838 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3344839 {_87099 : Type'} (f : type686 _87099) (x : _87099 -> Prop) : (f x) = (@I ((_87099 -> Prop) -> Prop) f x).
Proof. exact (@lem3344838 (_87099 -> Prop) Prop f x). Qed.
Lemma lem3344841 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) : (t t') = (@I ((_87099 -> Prop) -> Prop) t t').
Proof. exact (@lem3344839 _87099 t t'). Qed.
Lemma lem3344842 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) : (term181 _87099 t t') = (term182 _87099 t t').
Proof. exact (MK_COMB (@lem3344833) (@lem3344841 _87099 t t')). Qed.
Lemma lem3344843 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3344844 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) : (term192 _87099 t t') = (term193 _87099 t t').
Proof. exact (MK_COMB (@lem3344843) (@lem3344842 _87099 t t')). Qed.
Lemma lem3344845 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term79 _87099 t t' x) = (term194 _87099 t t' x).
Proof. exact (MK_COMB (@lem3344844 _87099 t t') (@lem3344832 _87099 t' x)). Qed.
Lemma lem3344846 {_87099 : Type'} (t : type686 _87099) (x : _87099) : (term85 _87099 t x) = (term195 _87099 t x).
Proof. exact (fun_ext (fun t' : _87099 -> Prop => @lem3344845 _87099 t t' x)). Qed.
Lemma lem3344847 {_87099 : Type'} : (@all (_87099 -> Prop)) = (@all (_87099 -> Prop)).
Proof. exact (eq_refl (@all (_87099 -> Prop))). Qed.
Lemma lem3344848 {_87099 : Type'} (t : type686 _87099) (x : _87099) : (term86 _87099 t x) = (term196 _87099 t x).
Proof. exact (MK_COMB (@lem3344847 _87099) (@lem3344846 _87099 t x)). Qed.
Lemma lem3344849 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3344854 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3344855 {_87099 : Type'} (f : _87099 -> Prop) (x : _87099) : (f x) = (@I (_87099 -> Prop) f x).
Proof. exact (@lem3344854 _87099 Prop f x). Qed.
Lemma lem3344857 {_87099 : Type'} (t : _87099 -> Prop) (x : _87099) : (t x) = (@I (_87099 -> Prop) t x).
Proof. exact (@lem3344855 _87099 t x). Qed.
Lemma lem3344858 {_87099 : Type'} (t : _87099 -> Prop) (x : _87099) : (term63 _87099 t x) = (term180 _87099 t x).
Proof. exact (MK_COMB (@lem3344849) (@lem3344857 _87099 t x)). Qed.
Lemma lem3344859 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3344864 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3344865 {_87099 : Type'} (f : type686 _87099) (x : _87099 -> Prop) : (f x) = (@I ((_87099 -> Prop) -> Prop) f x).
Proof. exact (@lem3344864 (_87099 -> Prop) Prop f x). Qed.
Lemma lem3344867 {_87099 : Type'} (s : type686 _87099) (t : _87099 -> Prop) : (s t) = (@I ((_87099 -> Prop) -> Prop) s t).
Proof. exact (@lem3344865 _87099 s t). Qed.
Lemma lem3344868 {_87099 : Type'} (s : type686 _87099) (t : _87099 -> Prop) : (term181 _87099 s t) = (term182 _87099 s t).
Proof. exact (MK_COMB (@lem3344859) (@lem3344867 _87099 s t)). Qed.
Lemma lem3344869 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3344870 {_87099 : Type'} (s : type686 _87099) (t : _87099 -> Prop) : (term192 _87099 s t) = (term193 _87099 s t).
Proof. exact (MK_COMB (@lem3344869) (@lem3344868 _87099 s t)). Qed.
Lemma lem3344871 {_87099 : Type'} (s : type686 _87099) (t : _87099 -> Prop) (x : _87099) : (term79 _87099 s t x) = (term194 _87099 s t x).
Proof. exact (MK_COMB (@lem3344870 _87099 s t) (@lem3344858 _87099 t x)). Qed.
Lemma lem3344872 {_87099 : Type'} (s : type686 _87099) (x : _87099) : (term85 _87099 s x) = (term195 _87099 s x).
Proof. exact (fun_ext (fun t : _87099 -> Prop => @lem3344871 _87099 s t x)). Qed.
Lemma lem3344873 {_87099 : Type'} : (@all (_87099 -> Prop)) = (@all (_87099 -> Prop)).
Proof. exact (eq_refl (@all (_87099 -> Prop))). Qed.
Lemma lem3344874 {_87099 : Type'} (s : type686 _87099) (x : _87099) : (term86 _87099 s x) = (term196 _87099 s x).
Proof. exact (MK_COMB (@lem3344873 _87099) (@lem3344872 _87099 s x)). Qed.
Lemma lem3344875 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3344876 {_87099 : Type'} (s : type686 _87099) (x : _87099) : (term88 _87099 s x) = (term197 _87099 s x).
Proof. exact (MK_COMB (@lem3344875) (@lem3344874 _87099 s x)). Qed.
Lemma lem3344877 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term90 _87099 s t x) = (term198 _87099 s t x).
Proof. exact (MK_COMB (@lem3344876 _87099 s x) (@lem3344848 _87099 t x)). Qed.
Lemma lem3344882 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3344883 {_87099 : Type'} (f : _87099 -> Prop) (x : _87099) : (f x) = (@I (_87099 -> Prop) f x).
Proof. exact (@lem3344882 _87099 Prop f x). Qed.
Lemma lem3344885 {_87099 : Type'} (t' : _87099 -> Prop) (x : _87099) : (t' x) = (@I (_87099 -> Prop) t' x).
Proof. exact (@lem3344883 _87099 t' x). Qed.
Lemma lem3344890 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3344891 {_87099 : Type'} (f : type686 _87099) (x : _87099 -> Prop) : (f x) = (@I ((_87099 -> Prop) -> Prop) f x).
Proof. exact (@lem3344890 (_87099 -> Prop) Prop f x). Qed.
Lemma lem3344893 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) : (t t') = (@I ((_87099 -> Prop) -> Prop) t t').
Proof. exact (@lem3344891 _87099 t t'). Qed.
Lemma lem3344898 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3344899 {_87099 : Type'} (f : type686 _87099) (x : _87099 -> Prop) : (f x) = (@I ((_87099 -> Prop) -> Prop) f x).
Proof. exact (@lem3344898 (_87099 -> Prop) Prop f x). Qed.
Lemma lem3344901 {_87099 : Type'} (s : type686 _87099) (t' : _87099 -> Prop) : (s t') = (@I ((_87099 -> Prop) -> Prop) s t').
Proof. exact (@lem3344899 _87099 s t'). Qed.
Lemma lem3344902 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3344903 {_87099 : Type'} (s : type686 _87099) (t' : _87099 -> Prop) : (term21 _87099 s t') = (term199 _87099 s t').
Proof. exact (MK_COMB (@lem3344902) (@lem3344901 _87099 s t')). Qed.
Lemma lem3344904 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) : (term22 _87099 s t t') = (term200 _87099 s t t').
Proof. exact (MK_COMB (@lem3344903 _87099 s t') (@lem3344893 _87099 t t')). Qed.
Lemma lem3344905 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3344906 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) : (term24 _87099 s t t') = (term201 _87099 s t t').
Proof. exact (MK_COMB (@lem3344905) (@lem3344904 _87099 s t t')). Qed.
Lemma lem3344907 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term26 _87099 s t t' x) = (term202 _87099 s t t' x).
Proof. exact (MK_COMB (@lem3344906 _87099 s t t') (@lem3344885 _87099 t' x)). Qed.
Lemma lem3344908 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3344909 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term115 _87099 s t t' x) = (term203 _87099 s t t' x).
Proof. exact (MK_COMB (@lem3344908) (@lem3344907 _87099 s t t' x)). Qed.
Lemma lem3344910 {_87099 : Type'} (t' : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term117 _87099 t' s t x) = (term204 _87099 t' s t x).
Proof. exact (MK_COMB (@lem3344909 _87099 s t t' x) (@lem3344877 _87099 s t x)). Qed.
Lemma lem3344911 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3344912 {_87099 : Type'} (t' : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term170 _87099 t' s t x) = (term205 _87099 t' s t x).
Proof. exact (MK_COMB (@lem3344911) (@lem3344910 _87099 t' s t x)). Qed.
Lemma lem3344913 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term172 _87099 s t t' x) = (term206 _87099 s t t' x).
Proof. exact (MK_COMB (@lem3344912 _87099 t' s t x) (@lem3344822 _87099 s t t' x)). Qed.
Lemma lem3344914 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term172 _87099 s t t' x) : term206 _87099 s t t' x.
Proof. exact (EQ_MP (@lem3344913 _87099 s t t' x) (@lem3344739 _87099 s t t' x h1)). Qed.
Lemma lem3344915 {_87099 : Type'} (t' : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term204 _87099 t' s t x) : term204 _87099 t' s t x.
Proof. exact (h1). Qed.
Lemma lem3344916 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term191 _87099 s t t' x) : term191 _87099 s t t' x.
Proof. exact (h1). Qed.
Lemma lem3344917 {_87099 : Type'} (t' : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term204 _87099 t' s t x) : term198 _87099 s t x.
Proof. exact (proj2 (@lem3344915 _87099 t' s t x h1)). Qed.
Lemma lem3344918 {_87099 : Type'} (t' : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term204 _87099 t' s t x) : term202 _87099 s t t' x.
Proof. exact (proj1 (@lem3344915 _87099 t' s t x h1)). Qed.
Lemma lem3344919 {_87099 : Type'} (t' : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term204 _87099 t' s t x) : term196 _87099 t x.
Proof. exact (proj2 (@lem3344917 _87099 t' s t x h1)). Qed.
Lemma lem3344920 {_87099 : Type'} (t' : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term204 _87099 t' s t x) : term196 _87099 s x.
Proof. exact (proj1 (@lem3344917 _87099 t' s t x h1)). Qed.
Lemma lem3344922 {_87099 : Type'} (t' : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term204 _87099 t' s t x) : term200 _87099 s t t'.
Proof. exact (proj1 (@lem3344918 _87099 t' s t x h1)). Qed.
Lemma lem3344925 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term191 _87099 s t t' x) : term179 _87099 s t t' x.
Proof. exact (proj2 (@lem3344916 _87099 s t t' x h1)). Qed.
Lemma lem3344926 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term191 _87099 s t t' x) : term189 _87099 s t x.
Proof. exact (proj1 (@lem3344916 _87099 s t t' x h1)). Qed.
Lemma lem3344927 {_87099 : Type'} (s : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term177 _87099 s t' x) : term177 _87099 s t' x.
Proof. exact (h1). Qed.
Lemma lem3344928 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term177 _87099 t t' x) : term177 _87099 t t' x.
Proof. exact (h1). Qed.
Lemma lem3344940 {_87099 : Type'} (s : type686 _87099) (t : _87099 -> Prop) (x : _87099) : (term194 _87099 s t x) = (term194 _87099 s t x).
Proof. exact (eq_refl (term194 _87099 s t x)). Qed.
Lemma lem3344941 {_87099 : Type'} (s : type686 _87099) (x : _87099) : (term195 _87099 s x) = (term195 _87099 s x).
Proof. exact (fun_ext (fun t : _87099 -> Prop => @lem3344940 _87099 s t x)). Qed.
Lemma lem3344942 {_87099 : Type'} : (@all (_87099 -> Prop)) = (@all (_87099 -> Prop)).
Proof. exact (eq_refl (@all (_87099 -> Prop))). Qed.
Lemma lem3344944 {_87099 : Type'} (s : type686 _87099) (x : _87099) : (term196 _87099 s x) = (term196 _87099 s x).
Proof. exact (MK_COMB (@lem3344942 _87099) (@lem3344941 _87099 s x)). Qed.
Lemma lem3344945 {_87099 : Type'} (t' : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term204 _87099 t' s t x) : term196 _87099 s x.
Proof. exact (EQ_MP (@lem3344944 _87099 s x) (@lem3344920 _87099 t' s t x h1)). Qed.
Lemma lem3344966 {_87099 : Type'} (s : type686 _87099) (t' : _87099 -> Prop) (h1 : @I ((_87099 -> Prop) -> Prop) s t') : @I ((_87099 -> Prop) -> Prop) s t'.
Proof. exact (h1). Qed.
Lemma lem3344987 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term194 _87099 t t' x) = (term194 _87099 t t' x).
Proof. exact (eq_refl (term194 _87099 t t' x)). Qed.
Lemma lem3344988 {_87099 : Type'} (t : type686 _87099) (x : _87099) : (term195 _87099 t x) = (term195 _87099 t x).
Proof. exact (fun_ext (fun t' : _87099 -> Prop => @lem3344987 _87099 t t' x)). Qed.
Lemma lem3344989 {_87099 : Type'} : (@all (_87099 -> Prop)) = (@all (_87099 -> Prop)).
Proof. exact (eq_refl (@all (_87099 -> Prop))). Qed.
Lemma lem3344991 {_87099 : Type'} (t : type686 _87099) (x : _87099) : (term196 _87099 t x) = (term196 _87099 t x).
Proof. exact (MK_COMB (@lem3344989 _87099) (@lem3344988 _87099 t x)). Qed.
Lemma lem3344992 {_87099 : Type'} (t' : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term204 _87099 t' s t x) : term196 _87099 t x.
Proof. exact (EQ_MP (@lem3344991 _87099 t x) (@lem3344919 _87099 t' s t x h1)). Qed.
Lemma lem3345000 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) (h1 : @I ((_87099 -> Prop) -> Prop) t t') : @I ((_87099 -> Prop) -> Prop) t t'.
Proof. exact (h1). Qed.
Lemma lem3345018 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term187 _87099 s t t' x) = (term207 _87099 s t t' x).
Proof. exact (@lem19699 (term182 _87099 s t') (term182 _87099 t t') (term180 _87099 t' x)). Qed.
Lemma lem3345019 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term188 _87099 s t x) = (term208 _87099 s t x).
Proof. exact (fun_ext (fun t' : _87099 -> Prop => @lem3345018 _87099 s t t' x)). Qed.
Lemma lem3345020 {_87099 : Type'} : (@all (_87099 -> Prop)) = (@all (_87099 -> Prop)).
Proof. exact (eq_refl (@all (_87099 -> Prop))). Qed.
Lemma lem3345022 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term189 _87099 s t x) = (term209 _87099 s t x).
Proof. exact (MK_COMB (@lem3345020 _87099) (@lem3345019 _87099 s t x)). Qed.
Lemma lem3345023 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term191 _87099 s t t' x) : term209 _87099 s t x.
Proof. exact (EQ_MP (@lem3345022 _87099 s t x) (@lem3344926 _87099 s t t' x h1)). Qed.
Lemma lem3345049 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) : (term187 _87099 s t t' x) = (term207 _87099 s t t' x).
Proof. exact (@lem19699 (term182 _87099 s t') (term182 _87099 t t') (term180 _87099 t' x)). Qed.
Lemma lem3345050 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term188 _87099 s t x) = (term208 _87099 s t x).
Proof. exact (fun_ext (fun t' : _87099 -> Prop => @lem3345049 _87099 s t t' x)). Qed.
Lemma lem3345051 {_87099 : Type'} : (@all (_87099 -> Prop)) = (@all (_87099 -> Prop)).
Proof. exact (eq_refl (@all (_87099 -> Prop))). Qed.
Lemma lem3345053 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term189 _87099 s t x) = (term209 _87099 s t x).
Proof. exact (MK_COMB (@lem3345051 _87099) (@lem3345050 _87099 s t x)). Qed.
Lemma lem3345054 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term191 _87099 s t t' x) : term209 _87099 s t x.
Proof. exact (EQ_MP (@lem3345053 _87099 s t x) (@lem3344926 _87099 s t t' x h1)). Qed.
Lemma lem3345063 {_87099 : Type'} (_34893 : _87099 -> Prop) (t' : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term204 _87099 t' s t x) : term210 _87099 s x _34893.
Proof. exact (@lem3344945 _87099 t' s t x h1 _34893). Qed.
Lemma lem3345064 {_87099 : Type'} (s : type686 _87099) (_34893 : _87099 -> Prop) (x : _87099) : (term210 _87099 s x _34893) = (term194 _87099 s _34893 x).
Proof. exact (eq_refl (term210 _87099 s x _34893)). Qed.
Lemma lem3345072 {_87099 : Type'} (_34896 : _87099 -> Prop) (t' : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term204 _87099 t' s t x) : term210 _87099 t x _34896.
Proof. exact (@lem3344992 _87099 t' s t x h1 _34896). Qed.
Lemma lem3345073 {_87099 : Type'} (t : type686 _87099) (_34896 : _87099 -> Prop) (x : _87099) : (term210 _87099 t x _34896) = (term194 _87099 t _34896 x).
Proof. exact (eq_refl (term210 _87099 t x _34896)). Qed.
Lemma lem3345075 {_87099 : Type'} (_34897 : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term191 _87099 s t t' x) : term211 _87099 s t x _34897.
Proof. exact (@lem3345023 _87099 s t t' x h1 _34897). Qed.
Lemma lem3345076 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (_34897 : _87099 -> Prop) (x : _87099) : (term211 _87099 s t x _34897) = (term207 _87099 s t _34897 x).
Proof. exact (eq_refl (term211 _87099 s t x _34897)). Qed.
Lemma lem3345077 {_87099 : Type'} (_34897 : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term191 _87099 s t t' x) : term207 _87099 s t _34897 x.
Proof. exact (EQ_MP (@lem3345076 _87099 s t _34897 x) (@lem3345075 _87099 _34897 s t t' x h1)). Qed.
Lemma lem3345078 {_87099 : Type'} (_34898 : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term191 _87099 s t t' x) : term211 _87099 s t x _34898.
Proof. exact (@lem3345054 _87099 s t t' x h1 _34898). Qed.
Lemma lem3345079 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (_34898 : _87099 -> Prop) (x : _87099) : (term211 _87099 s t x _34898) = (term207 _87099 s t _34898 x).
Proof. exact (eq_refl (term211 _87099 s t x _34898)). Qed.
Lemma lem3345080 {_87099 : Type'} (_34898 : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term191 _87099 s t t' x) : term207 _87099 s t _34898 x.
Proof. exact (EQ_MP (@lem3345079 _87099 s t _34898 x) (@lem3345078 _87099 _34898 s t t' x h1)). Qed.
Lemma lem3345090 {_87099 : Type'} (_34893 : _87099 -> Prop) (t' : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term204 _87099 t' s t x) : term194 _87099 s _34893 x.
Proof. exact (EQ_MP (@lem3345064 _87099 s _34893 x) (@lem3345063 _87099 _34893 t' s t x h1)). Qed.
Lemma lem3345100 {_87099 : Type'} (s : type686 _87099) (t' : _87099 -> Prop) (h1 : @I ((_87099 -> Prop) -> Prop) s t') : @I ((_87099 -> Prop) -> Prop) s t'.
Proof. exact (h1). Qed.
Lemma lem3345112 {_87099 : Type'} (_34896 : _87099 -> Prop) (t' : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term204 _87099 t' s t x) : term194 _87099 t _34896 x.
Proof. exact (EQ_MP (@lem3345073 _87099 t _34896 x) (@lem3345072 _87099 _34896 t' s t x h1)). Qed.
Lemma lem3345116 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) (h1 : @I ((_87099 -> Prop) -> Prop) t t') : @I ((_87099 -> Prop) -> Prop) t t'.
Proof. exact (h1). Qed.
Lemma lem3345126 {_87099 : Type'} (_34897 : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term191 _87099 s t t' x) : term194 _87099 s _34897 x.
Proof. exact (proj1 (@lem3345077 _87099 _34897 s t t' x h1)). Qed.
Lemma lem3345148 {_87099 : Type'} (_34898 : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term191 _87099 s t t' x) : term194 _87099 t _34898 x.
Proof. exact (proj2 (@lem3345080 _87099 _34898 s t t' x h1)). Qed.
Lemma lem3345150 {_87099 : Type'} (s : type686 _87099) (t' : _87099 -> Prop) (h1 : @I ((_87099 -> Prop) -> Prop) s t') : @I ((_87099 -> Prop) -> Prop) s t'.
Proof. exact (h1). Qed.
Lemma lem3345151 {_87099 : Type'} (s : type686 _87099) (t' : _87099 -> Prop) (h1 : @I ((_87099 -> Prop) -> Prop) s t') : term212 _87099 s t'.
Proof. exact (fun h0 : term182 _87099 s t' => @lem3345150 _87099 s t' h1). Qed.
Lemma lem3345153 (p : Prop) : (term213 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3345154 {_87099 : Type'} (s : type686 _87099) (t' : _87099 -> Prop) : (term212 _87099 s t') = (@I ((_87099 -> Prop) -> Prop) s t').
Proof. exact (@lem3345153 (@I ((_87099 -> Prop) -> Prop) s t')). Qed.
Lemma lem3345155 {_87099 : Type'} (s : type686 _87099) (t' : _87099 -> Prop) (h1 : @I ((_87099 -> Prop) -> Prop) s t') : @I ((_87099 -> Prop) -> Prop) s t'.
Proof. exact (EQ_MP (@lem3345154 _87099 s t') (@lem3345151 _87099 s t' h1)). Qed.
Lemma lem3345157 {_87099 : Type'} (t' : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term204 _87099 t' s t x) : @I (_87099 -> Prop) t' x.
Proof. exact (proj2 (@lem3344918 _87099 t' s t x h1)). Qed.
Lemma lem3345158 {_87099 : Type'} (t' : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term204 _87099 t' s t x) : term214 _87099 t' x.
Proof. exact (fun h0 : term180 _87099 t' x => @lem3345157 _87099 t' s t x h1). Qed.
Lemma lem3345160 (p : Prop) : (term213 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3345161 {_87099 : Type'} (t' : _87099 -> Prop) (x : _87099) : (term214 _87099 t' x) = (@I (_87099 -> Prop) t' x).
Proof. exact (@lem3345160 (@I (_87099 -> Prop) t' x)). Qed.
Lemma lem3345162 {_87099 : Type'} (t' : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term204 _87099 t' s t x) : @I (_87099 -> Prop) t' x.
Proof. exact (EQ_MP (@lem3345161 _87099 t' x) (@lem3345158 _87099 t' s t x h1)). Qed.
Lemma lem3345164 (a : Prop) (b : Prop) : (term215 a b) = (term216 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3345165 {_87099 : Type'} (s : type686 _87099) (_34893 : _87099 -> Prop) (x : _87099) : (term194 _87099 s _34893 x) = (term217 _87099 s _34893 x).
Proof. exact (@lem3345164 (@I ((_87099 -> Prop) -> Prop) s _34893) (@I (_87099 -> Prop) _34893 x)). Qed.
Lemma lem3345167 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3345168 {_87099 : Type'} (s : type686 _87099) (_34893 : _87099 -> Prop) (x : _87099) : (term217 _87099 s _34893 x) = (term218 _87099 s _34893 x).
Proof. exact (@lem3345167 (term177 _87099 s _34893 x)). Qed.
Lemma lem3345169 {_87099 : Type'} (s : type686 _87099) (_34893 : _87099 -> Prop) (x : _87099) : (term194 _87099 s _34893 x) = (term218 _87099 s _34893 x).
Proof. exact (TRANS (@lem3345165 _87099 s _34893 x) (@lem3345168 _87099 s _34893 x)). Qed.
Lemma lem3345171 {_87099 : Type'} (t : type686 _87099) (x : _87099) (s : type686 _87099) (t' : _87099 -> Prop) (h1 : term204 _87099 t' s t x) (h2 : @I ((_87099 -> Prop) -> Prop) s t') : term177 _87099 s t' x.
Proof. exact (conj (@lem3345155 _87099 s t' h2) (@lem3345162 _87099 t' s t x h1)). Qed.
Lemma lem3345173 {_87099 : Type'} (_34893 : _87099 -> Prop) (t' : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term204 _87099 t' s t x) : term218 _87099 s _34893 x.
Proof. exact (EQ_MP (@lem3345169 _87099 s _34893 x) (@lem3345090 _87099 _34893 t' s t x h1)). Qed.
Lemma lem3345174 {_87099 : Type'} (_34893 : _87099 -> Prop) (t' : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term204 _87099 t' s t x) : term218 _87099 s _34893 x.
Proof. exact (@lem3345173 _87099 _34893 t' s t x h1). Qed.
Lemma lem3345175 {_87099 : Type'} (t' : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term204 _87099 t' s t x) : term218 _87099 s t' x.
Proof. exact (@lem3345174 _87099 t' t' s t x h1). Qed.
Lemma lem3345178 {_87099 : Type'} (t : type686 _87099) (x : _87099) (s : type686 _87099) (t' : _87099 -> Prop) (h1 : term204 _87099 t' s t x) (h2 : @I ((_87099 -> Prop) -> Prop) s t') : False.
Proof. exact (@lem3345175 _87099 t' s t x h1 (@lem3345171 _87099 t x s t' h1 h2)). Qed.
Lemma lem3345179 {_87099 : Type'} (t : type686 _87099) (x : _87099) (s : type686 _87099) (t' : _87099 -> Prop) (h1 : term204 _87099 t' s t x) (h2 : @I ((_87099 -> Prop) -> Prop) s t') : term219.
Proof. exact (fun h0 : ~ False => @lem3345178 _87099 t x s t' h1 h2). Qed.
Lemma lem3345181 (p : Prop) : (term213 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3345182 : term219 = False.
Proof. exact (@lem3345181 False). Qed.
Lemma lem3345183 {_87099 : Type'} (t : type686 _87099) (x : _87099) (s : type686 _87099) (t' : _87099 -> Prop) (h1 : term204 _87099 t' s t x) (h2 : @I ((_87099 -> Prop) -> Prop) s t') : False.
Proof. exact (EQ_MP (@lem3345182) (@lem3345179 _87099 t x s t' h1 h2)). Qed.
Lemma lem3345185 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) (h1 : @I ((_87099 -> Prop) -> Prop) t t') : @I ((_87099 -> Prop) -> Prop) t t'.
Proof. exact (h1). Qed.
Lemma lem3345186 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) (h1 : @I ((_87099 -> Prop) -> Prop) t t') : term212 _87099 t t'.
Proof. exact (fun h0 : term182 _87099 t t' => @lem3345185 _87099 t t' h1). Qed.
Lemma lem3345188 (p : Prop) : (term213 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3345189 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) : (term212 _87099 t t') = (@I ((_87099 -> Prop) -> Prop) t t').
Proof. exact (@lem3345188 (@I ((_87099 -> Prop) -> Prop) t t')). Qed.
Lemma lem3345190 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) (h1 : @I ((_87099 -> Prop) -> Prop) t t') : @I ((_87099 -> Prop) -> Prop) t t'.
Proof. exact (EQ_MP (@lem3345189 _87099 t t') (@lem3345186 _87099 t t' h1)). Qed.
Lemma lem3345192 {_87099 : Type'} (t' : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term204 _87099 t' s t x) : @I (_87099 -> Prop) t' x.
Proof. exact (proj2 (@lem3344918 _87099 t' s t x h1)). Qed.
Lemma lem3345193 {_87099 : Type'} (t' : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term204 _87099 t' s t x) : term214 _87099 t' x.
Proof. exact (fun h0 : term180 _87099 t' x => @lem3345192 _87099 t' s t x h1). Qed.
Lemma lem3345195 (p : Prop) : (term213 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3345196 {_87099 : Type'} (t' : _87099 -> Prop) (x : _87099) : (term214 _87099 t' x) = (@I (_87099 -> Prop) t' x).
Proof. exact (@lem3345195 (@I (_87099 -> Prop) t' x)). Qed.
Lemma lem3345197 {_87099 : Type'} (t' : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term204 _87099 t' s t x) : @I (_87099 -> Prop) t' x.
Proof. exact (EQ_MP (@lem3345196 _87099 t' x) (@lem3345193 _87099 t' s t x h1)). Qed.
Lemma lem3345199 (a : Prop) (b : Prop) : (term215 a b) = (term216 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3345200 {_87099 : Type'} (t : type686 _87099) (_34896 : _87099 -> Prop) (x : _87099) : (term194 _87099 t _34896 x) = (term217 _87099 t _34896 x).
Proof. exact (@lem3345199 (@I ((_87099 -> Prop) -> Prop) t _34896) (@I (_87099 -> Prop) _34896 x)). Qed.
Lemma lem3345202 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3345203 {_87099 : Type'} (t : type686 _87099) (_34896 : _87099 -> Prop) (x : _87099) : (term217 _87099 t _34896 x) = (term218 _87099 t _34896 x).
Proof. exact (@lem3345202 (term177 _87099 t _34896 x)). Qed.
Lemma lem3345204 {_87099 : Type'} (t : type686 _87099) (_34896 : _87099 -> Prop) (x : _87099) : (term194 _87099 t _34896 x) = (term218 _87099 t _34896 x).
Proof. exact (TRANS (@lem3345200 _87099 t _34896 x) (@lem3345203 _87099 t _34896 x)). Qed.
Lemma lem3345206 {_87099 : Type'} (s : type686 _87099) (x : _87099) (t : type686 _87099) (t' : _87099 -> Prop) (h1 : term204 _87099 t' s t x) (h2 : @I ((_87099 -> Prop) -> Prop) t t') : term177 _87099 t t' x.
Proof. exact (conj (@lem3345190 _87099 t t' h2) (@lem3345197 _87099 t' s t x h1)). Qed.
Lemma lem3345208 {_87099 : Type'} (_34896 : _87099 -> Prop) (t' : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term204 _87099 t' s t x) : term218 _87099 t _34896 x.
Proof. exact (EQ_MP (@lem3345204 _87099 t _34896 x) (@lem3345112 _87099 _34896 t' s t x h1)). Qed.
Lemma lem3345209 {_87099 : Type'} (_34896 : _87099 -> Prop) (t' : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term204 _87099 t' s t x) : term218 _87099 t _34896 x.
Proof. exact (@lem3345208 _87099 _34896 t' s t x h1). Qed.
Lemma lem3345210 {_87099 : Type'} (t' : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term204 _87099 t' s t x) : term218 _87099 t t' x.
Proof. exact (@lem3345209 _87099 t' t' s t x h1). Qed.
Lemma lem3345213 {_87099 : Type'} (s : type686 _87099) (x : _87099) (t : type686 _87099) (t' : _87099 -> Prop) (h1 : term204 _87099 t' s t x) (h2 : @I ((_87099 -> Prop) -> Prop) t t') : False.
Proof. exact (@lem3345210 _87099 t' s t x h1 (@lem3345206 _87099 s x t t' h1 h2)). Qed.
Lemma lem3345214 {_87099 : Type'} (s : type686 _87099) (x : _87099) (t : type686 _87099) (t' : _87099 -> Prop) (h1 : term204 _87099 t' s t x) (h2 : @I ((_87099 -> Prop) -> Prop) t t') : term219.
Proof. exact (fun h0 : ~ False => @lem3345213 _87099 s x t t' h1 h2). Qed.
Lemma lem3345216 (p : Prop) : (term213 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3345217 : term219 = False.
Proof. exact (@lem3345216 False). Qed.
Lemma lem3345218 {_87099 : Type'} (s : type686 _87099) (x : _87099) (t : type686 _87099) (t' : _87099 -> Prop) (h1 : term204 _87099 t' s t x) (h2 : @I ((_87099 -> Prop) -> Prop) t t') : False.
Proof. exact (EQ_MP (@lem3345217) (@lem3345214 _87099 s x t t' h1 h2)). Qed.
Lemma lem3345220 {_87099 : Type'} (s : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term177 _87099 s t' x) : @I ((_87099 -> Prop) -> Prop) s t'.
Proof. exact (proj1 (@lem3344927 _87099 s t' x h1)). Qed.
Lemma lem3345221 {_87099 : Type'} (s : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term177 _87099 s t' x) : term212 _87099 s t'.
Proof. exact (fun h0 : term182 _87099 s t' => @lem3345220 _87099 s t' x h1). Qed.
Lemma lem3345223 (p : Prop) : (term213 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3345224 {_87099 : Type'} (s : type686 _87099) (t' : _87099 -> Prop) : (term212 _87099 s t') = (@I ((_87099 -> Prop) -> Prop) s t').
Proof. exact (@lem3345223 (@I ((_87099 -> Prop) -> Prop) s t')). Qed.
Lemma lem3345225 {_87099 : Type'} (s : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term177 _87099 s t' x) : @I ((_87099 -> Prop) -> Prop) s t'.
Proof. exact (EQ_MP (@lem3345224 _87099 s t') (@lem3345221 _87099 s t' x h1)). Qed.
Lemma lem3345227 {_87099 : Type'} (s : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term177 _87099 s t' x) : @I (_87099 -> Prop) t' x.
Proof. exact (proj2 (@lem3344927 _87099 s t' x h1)). Qed.
Lemma lem3345228 {_87099 : Type'} (s : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term177 _87099 s t' x) : term214 _87099 t' x.
Proof. exact (fun h0 : term180 _87099 t' x => @lem3345227 _87099 s t' x h1). Qed.
Lemma lem3345230 (p : Prop) : (term213 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3345231 {_87099 : Type'} (t' : _87099 -> Prop) (x : _87099) : (term214 _87099 t' x) = (@I (_87099 -> Prop) t' x).
Proof. exact (@lem3345230 (@I (_87099 -> Prop) t' x)). Qed.
Lemma lem3345232 {_87099 : Type'} (s : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term177 _87099 s t' x) : @I (_87099 -> Prop) t' x.
Proof. exact (EQ_MP (@lem3345231 _87099 t' x) (@lem3345228 _87099 s t' x h1)). Qed.
Lemma lem3345234 (a : Prop) (b : Prop) : (term215 a b) = (term216 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3345235 {_87099 : Type'} (s : type686 _87099) (_34897 : _87099 -> Prop) (x : _87099) : (term194 _87099 s _34897 x) = (term217 _87099 s _34897 x).
Proof. exact (@lem3345234 (@I ((_87099 -> Prop) -> Prop) s _34897) (@I (_87099 -> Prop) _34897 x)). Qed.
Lemma lem3345237 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3345238 {_87099 : Type'} (s : type686 _87099) (_34897 : _87099 -> Prop) (x : _87099) : (term217 _87099 s _34897 x) = (term218 _87099 s _34897 x).
Proof. exact (@lem3345237 (term177 _87099 s _34897 x)). Qed.
Lemma lem3345239 {_87099 : Type'} (s : type686 _87099) (_34897 : _87099 -> Prop) (x : _87099) : (term194 _87099 s _34897 x) = (term218 _87099 s _34897 x).
Proof. exact (TRANS (@lem3345235 _87099 s _34897 x) (@lem3345238 _87099 s _34897 x)). Qed.
Lemma lem3345241 {_87099 : Type'} (s : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term177 _87099 s t' x) : term177 _87099 s t' x.
Proof. exact (conj (@lem3345225 _87099 s t' x h1) (@lem3345232 _87099 s t' x h1)). Qed.
Lemma lem3345243 {_87099 : Type'} (_34897 : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term191 _87099 s t t' x) : term218 _87099 s _34897 x.
Proof. exact (EQ_MP (@lem3345239 _87099 s _34897 x) (@lem3345126 _87099 _34897 s t t' x h1)). Qed.
Lemma lem3345244 {_87099 : Type'} (_34897 : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term191 _87099 s t t' x) : term218 _87099 s _34897 x.
Proof. exact (@lem3345243 _87099 _34897 s t t' x h1). Qed.
Lemma lem3345245 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term191 _87099 s t t' x) : term218 _87099 s t' x.
Proof. exact (@lem3345244 _87099 t' s t t' x h1). Qed.
Lemma lem3345248 {_87099 : Type'} (t : type686 _87099) (s : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term191 _87099 s t t' x) (h2 : term177 _87099 s t' x) : False.
Proof. exact (@lem3345245 _87099 s t t' x h1 (@lem3345241 _87099 s t' x h2)). Qed.
Lemma lem3345249 {_87099 : Type'} (t : type686 _87099) (s : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term191 _87099 s t t' x) (h2 : term177 _87099 s t' x) : term219.
Proof. exact (fun h0 : ~ False => @lem3345248 _87099 t s t' x h1 h2). Qed.
Lemma lem3345251 (p : Prop) : (term213 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3345252 : term219 = False.
Proof. exact (@lem3345251 False). Qed.
Lemma lem3345253 {_87099 : Type'} (t : type686 _87099) (s : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term191 _87099 s t t' x) (h2 : term177 _87099 s t' x) : False.
Proof. exact (EQ_MP (@lem3345252) (@lem3345249 _87099 t s t' x h1 h2)). Qed.
Lemma lem3345255 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term177 _87099 t t' x) : @I ((_87099 -> Prop) -> Prop) t t'.
Proof. exact (proj1 (@lem3344928 _87099 t t' x h1)). Qed.
Lemma lem3345256 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term177 _87099 t t' x) : term212 _87099 t t'.
Proof. exact (fun h0 : term182 _87099 t t' => @lem3345255 _87099 t t' x h1). Qed.
Lemma lem3345258 (p : Prop) : (term213 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3345259 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) : (term212 _87099 t t') = (@I ((_87099 -> Prop) -> Prop) t t').
Proof. exact (@lem3345258 (@I ((_87099 -> Prop) -> Prop) t t')). Qed.
Lemma lem3345260 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term177 _87099 t t' x) : @I ((_87099 -> Prop) -> Prop) t t'.
Proof. exact (EQ_MP (@lem3345259 _87099 t t') (@lem3345256 _87099 t t' x h1)). Qed.
Lemma lem3345262 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term177 _87099 t t' x) : @I (_87099 -> Prop) t' x.
Proof. exact (proj2 (@lem3344928 _87099 t t' x h1)). Qed.
Lemma lem3345263 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term177 _87099 t t' x) : term214 _87099 t' x.
Proof. exact (fun h0 : term180 _87099 t' x => @lem3345262 _87099 t t' x h1). Qed.
Lemma lem3345265 (p : Prop) : (term213 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3345266 {_87099 : Type'} (t' : _87099 -> Prop) (x : _87099) : (term214 _87099 t' x) = (@I (_87099 -> Prop) t' x).
Proof. exact (@lem3345265 (@I (_87099 -> Prop) t' x)). Qed.
Lemma lem3345267 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term177 _87099 t t' x) : @I (_87099 -> Prop) t' x.
Proof. exact (EQ_MP (@lem3345266 _87099 t' x) (@lem3345263 _87099 t t' x h1)). Qed.
Lemma lem3345269 (a : Prop) (b : Prop) : (term215 a b) = (term216 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3345270 {_87099 : Type'} (t : type686 _87099) (_34898 : _87099 -> Prop) (x : _87099) : (term194 _87099 t _34898 x) = (term217 _87099 t _34898 x).
Proof. exact (@lem3345269 (@I ((_87099 -> Prop) -> Prop) t _34898) (@I (_87099 -> Prop) _34898 x)). Qed.
Lemma lem3345272 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3345273 {_87099 : Type'} (t : type686 _87099) (_34898 : _87099 -> Prop) (x : _87099) : (term217 _87099 t _34898 x) = (term218 _87099 t _34898 x).
Proof. exact (@lem3345272 (term177 _87099 t _34898 x)). Qed.
Lemma lem3345274 {_87099 : Type'} (t : type686 _87099) (_34898 : _87099 -> Prop) (x : _87099) : (term194 _87099 t _34898 x) = (term218 _87099 t _34898 x).
Proof. exact (TRANS (@lem3345270 _87099 t _34898 x) (@lem3345273 _87099 t _34898 x)). Qed.
Lemma lem3345276 {_87099 : Type'} (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term177 _87099 t t' x) : term177 _87099 t t' x.
Proof. exact (conj (@lem3345260 _87099 t t' x h1) (@lem3345267 _87099 t t' x h1)). Qed.
Lemma lem3345278 {_87099 : Type'} (_34898 : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term191 _87099 s t t' x) : term218 _87099 t _34898 x.
Proof. exact (EQ_MP (@lem3345274 _87099 t _34898 x) (@lem3345148 _87099 _34898 s t t' x h1)). Qed.
Lemma lem3345279 {_87099 : Type'} (_34898 : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term191 _87099 s t t' x) : term218 _87099 t _34898 x.
Proof. exact (@lem3345278 _87099 _34898 s t t' x h1). Qed.
Lemma lem3345280 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term191 _87099 s t t' x) : term218 _87099 t t' x.
Proof. exact (@lem3345279 _87099 t' s t t' x h1). Qed.
Lemma lem3345283 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term191 _87099 s t t' x) (h2 : term177 _87099 t t' x) : False.
Proof. exact (@lem3345280 _87099 s t t' x h1 (@lem3345276 _87099 t t' x h2)). Qed.
Lemma lem3345284 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term191 _87099 s t t' x) (h2 : term177 _87099 t t' x) : term219.
Proof. exact (fun h0 : ~ False => @lem3345283 _87099 s t t' x h1 h2). Qed.
Lemma lem3345286 (p : Prop) : (term213 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3345287 : term219 = False.
Proof. exact (@lem3345286 False). Qed.
Lemma lem3345288 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term191 _87099 s t t' x) (h2 : term177 _87099 t t' x) : False.
Proof. exact (EQ_MP (@lem3345287) (@lem3345284 _87099 s t t' x h1 h2)). Qed.
Lemma lem3345289 {_87099 : Type'} (s : type686 _87099) (x : _87099) (t : type686 _87099) (t' : _87099 -> Prop) (h1 : term204 _87099 t' s t x) (h2 : @I ((_87099 -> Prop) -> Prop) t t') : (@I ((_87099 -> Prop) -> Prop) t t') = False.
Proof. exact (prop_ext (fun h3 : @I ((_87099 -> Prop) -> Prop) t t' => @lem3345218 _87099 s x t t' h1 h2) (fun h3 : False => @lem3345116 _87099 t t' h2)). Qed.
Lemma lem3345290 {_87099 : Type'} (s : type686 _87099) (x : _87099) (t : type686 _87099) (t' : _87099 -> Prop) (h1 : term204 _87099 t' s t x) (h2 : @I ((_87099 -> Prop) -> Prop) t t') : False.
Proof. exact (EQ_MP (@lem3345289 _87099 s x t t' h1 h2) (@lem3345116 _87099 t t' h2)). Qed.
Lemma lem3345291 {_87099 : Type'} (t : type686 _87099) (x : _87099) (s : type686 _87099) (t' : _87099 -> Prop) (h1 : term204 _87099 t' s t x) (h2 : @I ((_87099 -> Prop) -> Prop) s t') : (@I ((_87099 -> Prop) -> Prop) s t') = False.
Proof. exact (prop_ext (fun h3 : @I ((_87099 -> Prop) -> Prop) s t' => @lem3345183 _87099 t x s t' h1 h2) (fun h3 : False => @lem3345100 _87099 s t' h2)). Qed.
Lemma lem3345292 {_87099 : Type'} (t : type686 _87099) (x : _87099) (s : type686 _87099) (t' : _87099 -> Prop) (h1 : term204 _87099 t' s t x) (h2 : @I ((_87099 -> Prop) -> Prop) s t') : False.
Proof. exact (EQ_MP (@lem3345291 _87099 t x s t' h1 h2) (@lem3345100 _87099 s t' h2)). Qed.
Lemma lem3345293 {_87099 : Type'} (s : type686 _87099) (x : _87099) (t : type686 _87099) (t' : _87099 -> Prop) (h1 : term204 _87099 t' s t x) (h2 : @I ((_87099 -> Prop) -> Prop) t t') : (@I ((_87099 -> Prop) -> Prop) t t') = False.
Proof. exact (prop_ext (fun h3 : @I ((_87099 -> Prop) -> Prop) t t' => @lem3345290 _87099 s x t t' h1 h2) (fun h3 : False => @lem3345000 _87099 t t' h2)). Qed.
Lemma lem3345294 {_87099 : Type'} (s : type686 _87099) (x : _87099) (t : type686 _87099) (t' : _87099 -> Prop) (h1 : term204 _87099 t' s t x) (h2 : @I ((_87099 -> Prop) -> Prop) t t') : False.
Proof. exact (EQ_MP (@lem3345293 _87099 s x t t' h1 h2) (@lem3345000 _87099 t t' h2)). Qed.
Lemma lem3345295 {_87099 : Type'} (t : type686 _87099) (x : _87099) (s : type686 _87099) (t' : _87099 -> Prop) (h1 : term204 _87099 t' s t x) (h2 : @I ((_87099 -> Prop) -> Prop) s t') : (@I ((_87099 -> Prop) -> Prop) s t') = False.
Proof. exact (prop_ext (fun h3 : @I ((_87099 -> Prop) -> Prop) s t' => @lem3345292 _87099 t x s t' h1 h2) (fun h3 : False => @lem3344966 _87099 s t' h2)). Qed.
Lemma lem3345296 {_87099 : Type'} (t : type686 _87099) (x : _87099) (s : type686 _87099) (t' : _87099 -> Prop) (h1 : term204 _87099 t' s t x) (h2 : @I ((_87099 -> Prop) -> Prop) s t') : False.
Proof. exact (EQ_MP (@lem3345295 _87099 t x s t' h1 h2) (@lem3344966 _87099 s t' h2)). Qed.
Lemma lem3345297 {_87099 : Type'} (s : type686 _87099) (x : _87099) (t : type686 _87099) (t' : _87099 -> Prop) (h1 : term204 _87099 t' s t x) (h2 : @I ((_87099 -> Prop) -> Prop) t t') : (@I ((_87099 -> Prop) -> Prop) t t') = False.
Proof. exact (prop_ext (fun h3 : @I ((_87099 -> Prop) -> Prop) t t' => @lem3345294 _87099 s x t t' h1 h2) (fun h3 : False => @lem3345000 _87099 t t' h2)). Qed.
Lemma lem3345298 {_87099 : Type'} (s : type686 _87099) (x : _87099) (t : type686 _87099) (t' : _87099 -> Prop) (h1 : term204 _87099 t' s t x) (h2 : @I ((_87099 -> Prop) -> Prop) t t') : False.
Proof. exact (EQ_MP (@lem3345297 _87099 s x t t' h1 h2) (@lem3345000 _87099 t t' h2)). Qed.
Lemma lem3345299 {_87099 : Type'} (t : type686 _87099) (x : _87099) (s : type686 _87099) (t' : _87099 -> Prop) (h1 : term204 _87099 t' s t x) (h2 : @I ((_87099 -> Prop) -> Prop) s t') : (@I ((_87099 -> Prop) -> Prop) s t') = False.
Proof. exact (prop_ext (fun h3 : @I ((_87099 -> Prop) -> Prop) s t' => @lem3345296 _87099 t x s t' h1 h2) (fun h3 : False => @lem3344966 _87099 s t' h2)). Qed.
Lemma lem3345300 {_87099 : Type'} (t : type686 _87099) (x : _87099) (s : type686 _87099) (t' : _87099 -> Prop) (h1 : term204 _87099 t' s t x) (h2 : @I ((_87099 -> Prop) -> Prop) s t') : False.
Proof. exact (EQ_MP (@lem3345299 _87099 t x s t' h1 h2) (@lem3344966 _87099 s t' h2)). Qed.
Lemma lem3345301 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term191 _87099 s t t' x) : False.
Proof. exact (or_elim (@lem3344925 _87099 s t t' x h1) (fun h0 : term177 _87099 s t' x => @lem3345253 _87099 t s t' x h1 h0) (fun h0 : term177 _87099 t t' x => @lem3345288 _87099 s t t' x h1 h0)). Qed.
Lemma lem3345302 {_87099 : Type'} (t' : _87099 -> Prop) (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term204 _87099 t' s t x) : False.
Proof. exact (or_elim (@lem3344922 _87099 t' s t x h1) (fun h0 : @I ((_87099 -> Prop) -> Prop) s t' => @lem3345300 _87099 t x s t' h1 h0) (fun h0 : @I ((_87099 -> Prop) -> Prop) t t' => @lem3345298 _87099 s x t t' h1 h0)). Qed.
Lemma lem3345303 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (t' : _87099 -> Prop) (x : _87099) (h1 : term172 _87099 s t t' x) : False.
Proof. exact (or_elim (@lem3344914 _87099 s t t' x h1) (fun h0 : term204 _87099 t' s t x => @lem3345302 _87099 t' s t x h0) (fun h0 : term191 _87099 s t t' x => @lem3345301 _87099 s t t' x h0)). Qed.
Lemma lem3345304 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term60 _87099 s t x) : False.
Proof. exact (ex_elim (@lem3344738 _87099 s t x h1) (fun t' : _87099 -> Prop => fun h0 : term174 _87099 s t x t' => @lem3345303 _87099 s t t' x h0)). Qed.
Lemma lem3345305 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term60 _87099 s t x) : (term60 _87099 s t x) = False.
Proof. exact (prop_ext (fun h2 : term60 _87099 s t x => @lem3345304 _87099 s t x h1) (fun h2 : False => @lem3344277 _87099 s t x h1)). Qed.
Lemma lem3345306 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) (h1 : term60 _87099 s t x) : False.
Proof. exact (EQ_MP (@lem3345305 _87099 s t x h1) (@lem3344277 _87099 s t x h1)). Qed.
Lemma lem3345307 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : term59 _87099 s t x.
Proof. exact (fun h0 : term60 _87099 s t x => @lem3345306 _87099 s t x h0). Qed.
Lemma lem3345308 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) (x : _87099) : (term29 _87099 s t x) = (term43 _87099 s t x).
Proof. exact (EQ_MP (@lem3344276 _87099 s t x) (@lem3345307 _87099 s t x)). Qed.
Lemma lem3345313 {_87099 : Type'} (s : type686 _87099) (t : type686 _87099) : term46 _87099 s t.
Proof. exact (fun x : _87099 => @lem3345308 _87099 s t x). Qed.
Lemma lem3345318 {_87099 : Type'} (s : type686 _87099) : term48 _87099 s.
Proof. exact (fun t : type686 _87099 => @lem3345313 _87099 s t). Qed.
Lemma lem3345323 {_87099 : Type'} : term50 _87099.
Proof. exact (fun s : type686 _87099 => @lem3345318 _87099 s). Qed.
Lemma lem3345324 {_87099 : Type'} : term52 _87099.
Proof. exact (EQ_MP (@lem3344272 _87099) (@lem3345323 _87099)). Qed.
Lemma lem3345326 {_87099 : Type'} : term52 _87099.
Proof. exact (@lem3344042 _87099 (@lem3345324 _87099)). Qed.
Lemma lem3345327 {_87099 : Type'} (h1 : term53 _87099) : False.
Proof. exact (@lem3345326 _87099 (@lem3344026 _87099 h1)). Qed.
Lemma lem3345328 {_87099 : Type'} (h1 : term53 _87099) : (term53 _87099) = False.
Proof. exact (prop_ext (fun h2 : term53 _87099 => @lem3345327 _87099 h1) (fun h2 : False => @lem3344026 _87099 h1)). Qed.
Lemma lem3345329 {_87099 : Type'} (h1 : term53 _87099) : False.
Proof. exact (EQ_MP (@lem3345328 _87099 h1) (@lem3344026 _87099 h1)). Qed.
Lemma lem3345330 {_87099 : Type'} : term52 _87099.
Proof. exact (fun h0 : term53 _87099 => @lem3345329 _87099 h0). Qed.
Lemma lem3345331 {_87099 : Type'} : term50 _87099.
Proof. exact (EQ_MP (@lem3344025 _87099) (@lem3345330 _87099)). Qed.
Lemma lem3345332 {_87099 : Type'} : term11 _87099.
Proof. exact (EQ_MP (@lem3344021 _87099) (@lem3345331 _87099)). Qed.
Lemma lem3345333 {_87099 : Type'} : term10 _87099.
Proof. exact (EQ_MP (@lem3343860 _87099) (@lem3345332 _87099)). Qed.
