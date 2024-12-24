Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DELETE_INSERT_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm13473_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3315841 {A : Type'} (_474 : A -> Prop) (_475 : Prop) (_476 : type686 A) (_477 : A -> Prop) : (term0 A _476 _475 _474 _477) = (term1 A _474 _475 _476 _477).
Proof. exact (@lem13473 (A -> Prop) _474 _475 _476 _477). Qed.
Lemma lem3315842 {A : Type'} (_474 : A -> Prop) (_475 : Prop) (x : A) (s : A -> Prop) (y : A) (_477 : A -> Prop) : (term2 A x s y _475 _474 _477) = (term3 A _474 _475 x s y _477).
Proof. exact (@lem3315841 A _474 _475 (term4 A x s y) _477). Qed.
Lemma lem3315843 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term5 A x s y) = (term6 A x s y).
Proof. exact (@lem3315842 A (@DELETE A s y) (x = y) x s y (term7 A x s y)). Qed.
Lemma lem3315844 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term8 A x s y) = ((term9 A x s y) = (term7 A x s y)).
Proof. exact (eq_refl (term8 A x s y)). Qed.
Lemma lem3315845 {A : Type'} (x : A) (y : A) : (term10 A x y) = (term10 A x y).
Proof. exact (eq_refl (term10 A x y)). Qed.
Lemma lem3315846 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term11 A x s y) = (term12 A x s y).
Proof. exact (MK_COMB (@lem3315845 A x y) (@lem3315844 A x s y)). Qed.
Lemma lem3315847 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term13 A x s y) = ((term9 A x s y) = (@DELETE A s y)).
Proof. exact (eq_refl (term13 A x s y)). Qed.
Lemma lem3315848 {A : Type'} (x : A) (y : A) : (term14 A x y) = (term14 A x y).
Proof. exact (eq_refl (term14 A x y)). Qed.
Lemma lem3315849 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term15 A x s y) = (term16 A x s y).
Proof. exact (MK_COMB (@lem3315848 A x y) (@lem3315847 A x s y)). Qed.
Lemma lem3315850 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3315851 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term17 A x s y) = (term18 A x s y).
Proof. exact (MK_COMB (@lem3315850) (@lem3315849 A x s y)). Qed.
Lemma lem3315852 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term6 A x s y) = (term19 A x s y).
Proof. exact (MK_COMB (@lem3315851 A x s y) (@lem3315846 A x s y)). Qed.
Lemma lem3315853 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term5 A x s y) = ((term9 A x s y) = (term20 A x s y)).
Proof. exact (eq_refl (term5 A x s y)). Qed.
Lemma lem3315854 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3315855 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term21 A x s y) = (term22 A x s y).
Proof. exact (MK_COMB (@lem3315854) (@lem3315853 A x s y)). Qed.
Lemma lem3315856 {A : Type'} (x : A) (s : A -> Prop) (y : A) : ((term5 A x s y) = (term6 A x s y)) = (((term9 A x s y) = (term20 A x s y)) = (term19 A x s y)).
Proof. exact (MK_COMB (@lem3315855 A x s y) (@lem3315852 A x s y)). Qed.
Lemma lem3315857 {A : Type'} (x : A) (s : A -> Prop) (y : A) : ((term9 A x s y) = (term20 A x s y)) = (term19 A x s y).
Proof. exact (EQ_MP (@lem3315856 A x s y) (@lem3315843 A x s y)). Qed.
Lemma lem3315858 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term19 A x s y) = ((term9 A x s y) = (term20 A x s y)).
Proof. exact (SYM (@lem3315857 A x s y)). Qed.
Lemma lem3315859 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem3315876 {A : Type'} (x : A) (y : A) (h1 : term23 A x y) : term23 A x y.
Proof. exact (h1). Qed.
Lemma lem3315904 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term24 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3315905 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term24 A s t).
Proof. exact (@lem3315904 A s t). Qed.
Lemma lem3315906 {A : Type'} (x : A) (s : A -> Prop) (y : A) : ((term9 A x s y) = (@DELETE A s y)) = (term25 A x s y).
Proof. exact (@lem3315905 A (term9 A x s y) (@DELETE A s y)). Qed.
Lemma lem3315915 {A : Type'} (x : A) (y : A) : (term14 A x y) = (term14 A x y).
Proof. exact (eq_refl (term14 A x y)). Qed.
Lemma lem3315916 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term16 A x s y) = (term26 A x s y).
Proof. exact (MK_COMB (@lem3315915 A x y) (@lem3315906 A x s y)). Qed.
Lemma lem3315921 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term26 A x s y) = (term16 A x s y).
Proof. exact (SYM (@lem3315916 A x s y)). Qed.
Lemma lem3315935 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term27 A x s y) = (term28 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3315936 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term27 A x s y) = (term28 A s x y).
Proof. exact (@lem3315935 A s x y). Qed.
Lemma lem3315937 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term29 A x' x s y) = (term30 A x s x' y).
Proof. exact (@lem3315936 A (@INSERT A x s) x' y). Qed.
Lemma lem3315941 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term31 A x y s) = (term32 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3315942 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term31 A x y s) = (term32 A y x s).
Proof. exact (@lem3315941 A y x s). Qed.
Lemma lem3315943 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term31 A x' x s) = (term32 A x x' s).
Proof. exact (@lem3315942 A x x' s). Qed.
Lemma lem3315949 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3315950 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3315949 A P x). Qed.
Lemma lem3315951 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3315950 A s x'). Qed.
Lemma lem3315952 {A : Type'} (x' : A) (x : A) : (term33 A x' x) = (term33 A x' x).
Proof. exact (eq_refl (term33 A x' x)). Qed.
Lemma lem3315953 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term32 A x x' s) = (term34 A x s x').
Proof. exact (MK_COMB (@lem3315952 A x' x) (@lem3315951 A s x')). Qed.
Lemma lem3315956 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term31 A x' x s) = (term34 A x s x').
Proof. exact (TRANS (@lem3315943 A x x' s) (@lem3315953 A x s x')). Qed.
Lemma lem3315957 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3315958 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term35 A x' x s) = (term36 A x s x').
Proof. exact (MK_COMB (@lem3315957) (@lem3315956 A x s x')). Qed.
Lemma lem3315961 {A : Type'} (x' : A) (y : A) : (term23 A x' y) = (term23 A x' y).
Proof. exact (eq_refl (term23 A x' y)). Qed.
Lemma lem3315962 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term30 A x s x' y) = (term37 A x s x' y).
Proof. exact (MK_COMB (@lem3315958 A x s x') (@lem3315961 A x' y)). Qed.
Lemma lem3315965 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term29 A x' x s y) = (term37 A x s x' y).
Proof. exact (TRANS (@lem3315937 A x s x' y) (@lem3315962 A x s x' y)). Qed.
Lemma lem3315966 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3315967 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term38 A x' x s y) = (term39 A x s x' y).
Proof. exact (MK_COMB (@lem3315966) (@lem3315965 A x s x' y)). Qed.
Lemma lem3315969 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term27 A x s y) = (term28 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3315970 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term27 A x s y) = (term28 A s x y).
Proof. exact (@lem3315969 A s x y). Qed.
Lemma lem3315971 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term27 A x' s y) = (term28 A s x' y).
Proof. exact (@lem3315970 A s x' y). Qed.
Lemma lem3315975 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3315976 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3315975 A P x). Qed.
Lemma lem3315977 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3315976 A s x'). Qed.
Lemma lem3315978 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3315979 {A : Type'} (s : A -> Prop) (x' : A) : (term40 A x' s) = (term41 A s x').
Proof. exact (MK_COMB (@lem3315978) (@lem3315977 A s x')). Qed.
Lemma lem3315982 {A : Type'} (x' : A) (y : A) : (term23 A x' y) = (term23 A x' y).
Proof. exact (eq_refl (term23 A x' y)). Qed.
Lemma lem3315983 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term28 A s x' y) = (term42 A s x' y).
Proof. exact (MK_COMB (@lem3315979 A s x') (@lem3315982 A x' y)). Qed.
Lemma lem3315986 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term27 A x' s y) = (term42 A s x' y).
Proof. exact (TRANS (@lem3315971 A s x' y) (@lem3315983 A s x' y)). Qed.
Lemma lem3315987 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : ((term29 A x' x s y) = (term27 A x' s y)) = ((term37 A x s x' y) = (term42 A s x' y)).
Proof. exact (MK_COMB (@lem3315967 A x s x' y) (@lem3315986 A s x' y)). Qed.
Lemma lem3315990 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term43 A x s y) = (term44 A x s y).
Proof. exact (fun_ext (fun x' : A => @lem3315987 A x s x' y)). Qed.
Lemma lem3315991 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3315992 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term25 A x s y) = (term45 A x s y).
Proof. exact (MK_COMB (@lem3315991 A) (@lem3315990 A x s y)). Qed.
Lemma lem3315997 {A : Type'} (x : A) (y : A) : (term14 A x y) = (term14 A x y).
Proof. exact (eq_refl (term14 A x y)). Qed.
Lemma lem3315998 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term26 A x s y) = (term46 A x s y).
Proof. exact (MK_COMB (@lem3315997 A x y) (@lem3315992 A x s y)). Qed.
Lemma lem3316003 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term46 A x s y) = (term26 A x s y).
Proof. exact (SYM (@lem3315998 A x s y)). Qed.
Lemma lem3316005 (p : Prop) : p = (term47 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3316006 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term46 A x s y) = (term48 A x s y).
Proof. exact (@lem3316005 (term46 A x s y)). Qed.
Lemma lem3316007 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term48 A x s y) = (term46 A x s y).
Proof. exact (SYM (@lem3316006 A x s y)). Qed.
Lemma lem3316008 {A : Type'} (x : A) (s : A -> Prop) (y : A) (h1 : term49 A x s y) : term49 A x s y.
Proof. exact (h1). Qed.
Lemma lem3316011 {A : Type'} (x : A) (s : A -> Prop) (y : A) (h1 : term48 A x s y) : term48 A x s y.
Proof. exact (h1). Qed.
Lemma lem3316012 {A : Type'} (x : A) (s : A -> Prop) (y : A) : term50 A x s y.
Proof. exact (fun h0 : term48 A x s y => @lem3316011 A x s y h0). Qed.
Lemma lem3316013 {A : Type'} (x : A) (s : A -> Prop) (y : A) (h1 : term50 A x s y) : term50 A x s y.
Proof. exact (h1). Qed.
Lemma lem3316014 {A : Type'} (x : A) (s : A -> Prop) (y : A) (h1 : term48 A x s y) : term48 A x s y.
Proof. exact (h1). Qed.
Lemma lem3316015 {A : Type'} (x : A) (s : A -> Prop) (y : A) (h1 : term48 A x s y) (h2 : term50 A x s y) : term48 A x s y.
Proof. exact (@lem3316013 A x s y h2 (@lem3316014 A x s y h1)). Qed.
Lemma lem3316016 {A : Type'} (x : A) (s : A -> Prop) (y : A) (h1 : term48 A x s y) : term51 A x s y.
Proof. exact (fun h0 : term50 A x s y => @lem3316015 A x s y h1 h0). Qed.
Lemma lem3316017 {A : Type'} (x : A) (s : A -> Prop) (y : A) (h1 : term50 A x s y) : term50 A x s y.
Proof. exact (h1). Qed.
Lemma lem3316018 {A : Type'} (x : A) (s : A -> Prop) (y : A) (h1 : term48 A x s y) (h2 : term50 A x s y) : term48 A x s y.
Proof. exact (@lem3316016 A x s y h1 (@lem3316017 A x s y h2)). Qed.
Lemma lem3316019 {A : Type'} (x : A) (s : A -> Prop) (y : A) (h1 : term50 A x s y) : term50 A x s y.
Proof. exact (fun h0 : term48 A x s y => @lem3316018 A x s y h0 h1). Qed.
Lemma lem3316020 {A : Type'} (x : A) (s : A -> Prop) (y : A) : term52 A x s y.
Proof. exact (fun h0 : term50 A x s y => @lem3316019 A x s y h0). Qed.
Lemma lem3316023 {A : Type'} (x : A) (s : A -> Prop) (y : A) : term50 A x s y.
Proof. exact (@lem3316020 A x s y (@lem3316012 A x s y)). Qed.
Lemma lem3316024 {A : Type'} (x : A) (s : A -> Prop) (y : A) : term50 A x s y.
Proof. exact (@lem3316023 A x s y). Qed.
Lemma lem3316038 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3316039 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term48 A x s y) = (term53 A x s y).
Proof. exact (@lem3316038 (term49 A x s y)). Qed.
Lemma lem3316041 (t : Prop) : (term54 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3316042 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term53 A x s y) = (term46 A x s y).
Proof. exact (@lem3316041 (term46 A x s y)). Qed.
Lemma lem3316045 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term48 A x s y) = (term46 A x s y).
Proof. exact (TRANS (@lem3316039 A x s y) (@lem3316042 A x s y)). Qed.
Lemma lem3316056 {A : Type'} (s : A -> Prop) (y : A) : (term55 A s y) = (term56 A s y).
Proof. exact (fun_ext (fun x : A => @lem3316045 A x s y)). Qed.
Lemma lem3316057 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3316058 {A : Type'} (s : A -> Prop) (y : A) : (term57 A s y) = (term58 A s y).
Proof. exact (MK_COMB (@lem3316057 A) (@lem3316056 A s y)). Qed.
Lemma lem3316063 {A : Type'} (y : A) : (term59 A y) = (term60 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3316058 A s y)). Qed.
Lemma lem3316064 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3316065 {A : Type'} (y : A) : (term61 A y) = (term62 A y).
Proof. exact (MK_COMB (@lem3316064 A) (@lem3316063 A y)). Qed.
Lemma lem3316070 {A : Type'} : (term63 A) = (term64 A).
Proof. exact (fun_ext (fun y : A => @lem3316065 A y)). Qed.
Lemma lem3316071 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3316080 {A : Type'} : (term65 A) = (term66 A).
Proof. exact (MK_COMB (@lem3316071 A) (@lem3316070 A)). Qed.
Lemma lem3316101 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : ((term37 A x s x' y) = (term42 A s x' y)) = ((term37 A x s x' y) = (term42 A s x' y)).
Proof. exact (eq_refl ((term37 A x s x' y) = (term42 A s x' y))). Qed.
Lemma lem3316102 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term44 A x s y) = (term44 A x s y).
Proof. exact (fun_ext (fun x' : A => @lem3316101 A x s x' y)). Qed.
Lemma lem3316103 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3316104 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term45 A x s y) = (term45 A x s y).
Proof. exact (MK_COMB (@lem3316103 A) (@lem3316102 A x s y)). Qed.
Lemma lem3316107 {A : Type'} (x : A) (y : A) : (term14 A x y) = (term14 A x y).
Proof. exact (eq_refl (term14 A x y)). Qed.
Lemma lem3316108 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term46 A x s y) = (term46 A x s y).
Proof. exact (MK_COMB (@lem3316107 A x y) (@lem3316104 A x s y)). Qed.
Lemma lem3316109 {A : Type'} (s : A -> Prop) (y : A) : (term56 A s y) = (term56 A s y).
Proof. exact (fun_ext (fun x : A => @lem3316108 A x s y)). Qed.
Lemma lem3316110 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3316111 {A : Type'} (s : A -> Prop) (y : A) : (term58 A s y) = (term58 A s y).
Proof. exact (MK_COMB (@lem3316110 A) (@lem3316109 A s y)). Qed.
Lemma lem3316112 {A : Type'} (y : A) : (term60 A y) = (term60 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3316111 A s y)). Qed.
Lemma lem3316113 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3316114 {A : Type'} (y : A) : (term62 A y) = (term62 A y).
Proof. exact (MK_COMB (@lem3316113 A) (@lem3316112 A y)). Qed.
Lemma lem3316115 {A : Type'} : (term64 A) = (term64 A).
Proof. exact (fun_ext (fun y : A => @lem3316114 A y)). Qed.
Lemma lem3316116 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3316117 {A : Type'} : (term66 A) = (term66 A).
Proof. exact (MK_COMB (@lem3316116 A) (@lem3316115 A)). Qed.
Lemma lem3316152 {A : Type'} : (term65 A) = (term66 A).
Proof. exact (TRANS (@lem3316080 A) (@lem3316117 A)). Qed.
Lemma lem3316153 {A : Type'} : (term66 A) = (term65 A).
Proof. exact (SYM (@lem3316152 A)). Qed.
Lemma lem3316156 (p : Prop) : p = (term47 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3316157 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : ((term37 A x s x' y) = (term42 A s x' y)) = (term67 A x s x' y).
Proof. exact (@lem3316156 ((term37 A x s x' y) = (term42 A s x' y))). Qed.
Lemma lem3316158 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term67 A x s x' y) = ((term37 A x s x' y) = (term42 A s x' y)).
Proof. exact (SYM (@lem3316157 A x s x' y)). Qed.
Lemma lem3316159 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term68 A x s x' y) : term68 A x s x' y.
Proof. exact (h1). Qed.
Lemma lem3316165 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem3316174 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term69 A x s x') = (term70 A x s x').
Proof. exact (@lem17160 (x' = x) (s x')). Qed.
Lemma lem3316181 {A : Type'} (x' : A) (y : A) : (term71 A x' y) = (x' = y).
Proof. exact (@lem16933 (x' = y)). Qed.
Lemma lem3316182 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3316183 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term72 A x s x') = (term73 A x s x').
Proof. exact (MK_COMB (@lem3316182) (@lem3316174 A x s x')). Qed.
Lemma lem3316184 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term74 A x s x' y) = (term75 A x s x' y).
Proof. exact (MK_COMB (@lem3316183 A x s x') (@lem3316181 A x' y)). Qed.
Lemma lem3316185 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term76 A x s x' y) = (term74 A x s x' y).
Proof. exact (@lem17045 (term34 A x s x') (term23 A x' y)). Qed.
Lemma lem3316186 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term76 A x s x' y) = (term75 A x s x' y).
Proof. exact (TRANS (@lem3316185 A x s x' y) (@lem3316184 A x s x' y)). Qed.
Lemma lem3316195 {A : Type'} (x' : A) (y : A) : (term71 A x' y) = (x' = y).
Proof. exact (@lem16933 (x' = y)). Qed.
Lemma lem3316197 {A : Type'} (s : A -> Prop) (x' : A) : (term77 A s x') = (term77 A s x').
Proof. exact (eq_refl (term77 A s x')). Qed.
Lemma lem3316198 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term78 A s x' y) = (term79 A s x' y).
Proof. exact (MK_COMB (@lem3316197 A s x') (@lem3316195 A x' y)). Qed.
Lemma lem3316199 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term80 A s x' y) = (term78 A s x' y).
Proof. exact (@lem17045 (s x') (term23 A x' y)). Qed.
Lemma lem3316200 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term80 A s x' y) = (term79 A s x' y).
Proof. exact (TRANS (@lem3316199 A s x' y) (@lem3316198 A s x' y)). Qed.
Lemma lem3316203 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term42 A s x' y) = (term42 A s x' y).
Proof. exact (eq_refl (term42 A s x' y)). Qed.
Lemma lem3316204 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3316205 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term81 A x s x' y) = (term82 A x s x' y).
Proof. exact (MK_COMB (@lem3316204) (@lem3316186 A x s x' y)). Qed.
Lemma lem3316206 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term83 A x s x' y) = (term84 A x s x' y).
Proof. exact (MK_COMB (@lem3316205 A x s x' y) (@lem3316203 A s x' y)). Qed.
Lemma lem3316208 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term85 A x s x' y) = (term85 A x s x' y).
Proof. exact (eq_refl (term85 A x s x' y)). Qed.
Lemma lem3316209 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term86 A x s x' y) = (term87 A x s x' y).
Proof. exact (MK_COMB (@lem3316208 A x s x' y) (@lem3316200 A s x' y)). Qed.
Lemma lem3316210 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3316211 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term88 A x s x' y) = (term89 A x s x' y).
Proof. exact (MK_COMB (@lem3316210) (@lem3316209 A x s x' y)). Qed.
Lemma lem3316212 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term90 A x s x' y) = (term91 A x s x' y).
Proof. exact (MK_COMB (@lem3316211 A x s x' y) (@lem3316206 A x s x' y)). Qed.
Lemma lem3316213 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term68 A x s x' y) = (term90 A x s x' y).
Proof. exact (@lem17646 (term37 A x s x' y) (term42 A s x' y)). Qed.
Lemma lem3316218 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term68 A x s x' y) = (term91 A x s x' y).
Proof. exact (TRANS (@lem3316213 A x s x' y) (@lem3316212 A x s x' y)). Qed.
Lemma lem3316225 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem3316305 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term68 A x s x' y) : term91 A x s x' y.
Proof. exact (EQ_MP (@lem3316218 A x s x' y) (@lem3316159 A x s x' y h1)). Qed.
Lemma lem3316306 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term87 A x s x' y) : term87 A x s x' y.
Proof. exact (h1). Qed.
Lemma lem3316307 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term84 A x s x' y) : term84 A x s x' y.
Proof. exact (h1). Qed.
Lemma lem3316308 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term87 A x s x' y) : term79 A s x' y.
Proof. exact (proj2 (@lem3316306 A x s x' y h1)). Qed.
Lemma lem3316309 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term87 A x s x' y) : term37 A x s x' y.
Proof. exact (proj1 (@lem3316306 A x s x' y h1)). Qed.
Lemma lem3316311 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term87 A x s x' y) : term34 A x s x'.
Proof. exact (proj1 (@lem3316309 A x s x' y h1)). Qed.
Lemma lem3316318 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term84 A x s x' y) : term42 A s x' y.
Proof. exact (proj2 (@lem3316307 A x s x' y h1)). Qed.
Lemma lem3316319 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term84 A x s x' y) : term75 A x s x' y.
Proof. exact (proj1 (@lem3316307 A x s x' y h1)). Qed.
Lemma lem3316322 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term70 A x s x') : term70 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3316329 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem3316337 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3316353 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3316357 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem3316369 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3316373 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') : term92 A s x'.
Proof. exact (h1). Qed.
Lemma lem3316389 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem3316425 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem3316427 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem3316429 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term87 A x s x' y) : term23 A x' y.
Proof. exact (proj2 (@lem3316309 A x s x' y h1)). Qed.
Lemma lem3316431 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3316437 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term87 A x s x' y) : term23 A x' y.
Proof. exact (proj2 (@lem3316309 A x s x' y h1)). Qed.
Lemma lem3316439 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3316441 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem3316447 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3316449 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') : term92 A s x'.
Proof. exact (h1). Qed.
Lemma lem3316453 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term87 A x s x' y) : term23 A x' y.
Proof. exact (proj2 (@lem3316309 A x s x' y h1)). Qed.
Lemma lem3316457 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem3316473 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term84 A x s x' y) : term23 A x' y.
Proof. exact (proj2 (@lem3316318 A x s x' y h1)). Qed.
Lemma lem3316475 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem3316503 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem3316504 {A : Type'} (y : A) : (term93 A y) = (term93 A y).
Proof. exact (eq_refl (term93 A y)). Qed.
Lemma lem3316505 {A : Type'} (y : A) (x' : A) (x : A) (h1 : x' = x) : (term94 A y x') = (term94 A y x).
Proof. exact (MK_COMB (@lem3316504 A y) (@lem3316431 A x' x h1)). Qed.
Lemma lem3316506 {A : Type'} (x : A) (y : A) : (term94 A y x) = (term23 A x y).
Proof. exact (eq_refl (term94 A y x)). Qed.
Lemma lem3316507 {A : Type'} (y : A) (x' : A) : (term95 A y x') = (term95 A y x').
Proof. exact (eq_refl (term95 A y x')). Qed.
Lemma lem3316508 {A : Type'} (x' : A) (x : A) (y : A) : ((term94 A y x') = (term94 A y x)) = ((term94 A y x') = (term23 A x y)).
Proof. exact (MK_COMB (@lem3316507 A y x') (@lem3316506 A x y)). Qed.
Lemma lem3316509 {A : Type'} (x' : A) (y : A) : (term94 A y x') = (term23 A x' y).
Proof. exact (eq_refl (term94 A y x')). Qed.
Lemma lem3316510 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3316511 {A : Type'} (x' : A) (y : A) : (term95 A y x') = (term96 A x' y).
Proof. exact (MK_COMB (@lem3316510) (@lem3316509 A x' y)). Qed.
Lemma lem3316512 {A : Type'} (x : A) (y : A) : (term23 A x y) = (term23 A x y).
Proof. exact (eq_refl (term23 A x y)). Qed.
Lemma lem3316513 {A : Type'} (x' : A) (x : A) (y : A) : ((term94 A y x') = (term23 A x y)) = ((term23 A x' y) = (term23 A x y)).
Proof. exact (MK_COMB (@lem3316511 A x' y) (@lem3316512 A x y)). Qed.
Lemma lem3316514 {A : Type'} (x' : A) (x : A) (y : A) : ((term94 A y x') = (term94 A y x)) = ((term23 A x' y) = (term23 A x y)).
Proof. exact (TRANS (@lem3316508 A x' x y) (@lem3316513 A x' x y)). Qed.
Lemma lem3316515 {A : Type'} (y : A) (x' : A) (x : A) (h1 : x' = x) : (term23 A x' y) = (term23 A x y).
Proof. exact (EQ_MP (@lem3316514 A x' x y) (@lem3316505 A y x' x h1)). Qed.
Lemma lem3316516 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term87 A x s x' y) (h2 : x' = x) : term23 A x y.
Proof. exact (EQ_MP (@lem3316515 A y x' x h2) (@lem3316429 A x s x' y h1)). Qed.
Lemma lem3316544 {A : Type'} (y : A) : (term93 A y) = (term93 A y).
Proof. exact (eq_refl (term93 A y)). Qed.
Lemma lem3316545 {A : Type'} (x : A) (y : A) (h1 : x = y) : (term94 A y x) = (term97 A y).
Proof. exact (MK_COMB (@lem3316544 A y) (@lem3316503 A x y h1)). Qed.
Lemma lem3316546 {A : Type'} (y : A) : (term97 A y) = (term98 A y).
Proof. exact (eq_refl (term97 A y)). Qed.
Lemma lem3316547 {A : Type'} (y : A) (x : A) : (term95 A y x) = (term95 A y x).
Proof. exact (eq_refl (term95 A y x)). Qed.
Lemma lem3316548 {A : Type'} (x : A) (y : A) : ((term94 A y x) = (term97 A y)) = ((term94 A y x) = (term98 A y)).
Proof. exact (MK_COMB (@lem3316547 A y x) (@lem3316546 A y)). Qed.
Lemma lem3316549 {A : Type'} (x : A) (y : A) : (term94 A y x) = (term23 A x y).
Proof. exact (eq_refl (term94 A y x)). Qed.
Lemma lem3316550 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3316551 {A : Type'} (x : A) (y : A) : (term95 A y x) = (term96 A x y).
Proof. exact (MK_COMB (@lem3316550) (@lem3316549 A x y)). Qed.
Lemma lem3316552 {A : Type'} (y : A) : (term98 A y) = (term98 A y).
Proof. exact (eq_refl (term98 A y)). Qed.
Lemma lem3316553 {A : Type'} (x : A) (y : A) : ((term94 A y x) = (term98 A y)) = ((term23 A x y) = (term98 A y)).
Proof. exact (MK_COMB (@lem3316551 A x y) (@lem3316552 A y)). Qed.
Lemma lem3316554 {A : Type'} (x : A) (y : A) : ((term94 A y x) = (term97 A y)) = ((term23 A x y) = (term98 A y)).
Proof. exact (TRANS (@lem3316548 A x y) (@lem3316553 A x y)). Qed.
Lemma lem3316555 {A : Type'} (x : A) (y : A) (h1 : x = y) : (term23 A x y) = (term98 A y).
Proof. exact (EQ_MP (@lem3316554 A x y) (@lem3316545 A x y h1)). Qed.
Lemma lem3316556 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term87 A x s x' y) (h2 : x = y) (h3 : x' = x) : term98 A y.
Proof. exact (EQ_MP (@lem3316555 A x y h2) (@lem3316516 A s y x' x h1 h3)). Qed.
Lemma lem3316598 {A : Type'} (y : A) : (term93 A y) = (term93 A y).
Proof. exact (eq_refl (term93 A y)). Qed.
Lemma lem3316599 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : (term94 A y x') = (term97 A y).
Proof. exact (MK_COMB (@lem3316598 A y) (@lem3316441 A x' y h1)). Qed.
Lemma lem3316600 {A : Type'} (y : A) : (term97 A y) = (term98 A y).
Proof. exact (eq_refl (term97 A y)). Qed.
Lemma lem3316601 {A : Type'} (y : A) (x' : A) : (term95 A y x') = (term95 A y x').
Proof. exact (eq_refl (term95 A y x')). Qed.
Lemma lem3316602 {A : Type'} (x' : A) (y : A) : ((term94 A y x') = (term97 A y)) = ((term94 A y x') = (term98 A y)).
Proof. exact (MK_COMB (@lem3316601 A y x') (@lem3316600 A y)). Qed.
Lemma lem3316603 {A : Type'} (x' : A) (y : A) : (term94 A y x') = (term23 A x' y).
Proof. exact (eq_refl (term94 A y x')). Qed.
Lemma lem3316604 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3316605 {A : Type'} (x' : A) (y : A) : (term95 A y x') = (term96 A x' y).
Proof. exact (MK_COMB (@lem3316604) (@lem3316603 A x' y)). Qed.
Lemma lem3316606 {A : Type'} (y : A) : (term98 A y) = (term98 A y).
Proof. exact (eq_refl (term98 A y)). Qed.
Lemma lem3316607 {A : Type'} (x' : A) (y : A) : ((term94 A y x') = (term98 A y)) = ((term23 A x' y) = (term98 A y)).
Proof. exact (MK_COMB (@lem3316605 A x' y) (@lem3316606 A y)). Qed.
Lemma lem3316608 {A : Type'} (x' : A) (y : A) : ((term94 A y x') = (term97 A y)) = ((term23 A x' y) = (term98 A y)).
Proof. exact (TRANS (@lem3316602 A x' y) (@lem3316607 A x' y)). Qed.
Lemma lem3316609 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : (term23 A x' y) = (term98 A y).
Proof. exact (EQ_MP (@lem3316608 A x' y) (@lem3316599 A x' y h1)). Qed.
Lemma lem3316610 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = y) : term98 A y.
Proof. exact (EQ_MP (@lem3316609 A x' y h2) (@lem3316437 A x s x' y h1)). Qed.
Lemma lem3316611 {A : Type'} (x : A) : (term99 A x) = (term99 A x).
Proof. exact (eq_refl (term99 A x)). Qed.
Lemma lem3316612 {A : Type'} (x : A) (x' : A) (y : A) (h1 : x' = y) : (term100 A x x') = (term100 A x y).
Proof. exact (MK_COMB (@lem3316611 A x) (@lem3316441 A x' y h1)). Qed.
Lemma lem3316613 {A : Type'} (y : A) (x : A) : (term100 A x y) = (y = x).
Proof. exact (eq_refl (term100 A x y)). Qed.
Lemma lem3316614 {A : Type'} (x : A) (x' : A) : (term101 A x x') = (term101 A x x').
Proof. exact (eq_refl (term101 A x x')). Qed.
Lemma lem3316615 {A : Type'} (x' : A) (y : A) (x : A) : ((term100 A x x') = (term100 A x y)) = ((term100 A x x') = (y = x)).
Proof. exact (MK_COMB (@lem3316614 A x x') (@lem3316613 A y x)). Qed.
Lemma lem3316616 {A : Type'} (x' : A) (x : A) : (term100 A x x') = (x' = x).
Proof. exact (eq_refl (term100 A x x')). Qed.
Lemma lem3316617 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3316618 {A : Type'} (x' : A) (x : A) : (term101 A x x') = (term102 A x' x).
Proof. exact (MK_COMB (@lem3316617) (@lem3316616 A x' x)). Qed.
Lemma lem3316619 {A : Type'} (y : A) (x : A) : (y = x) = (y = x).
Proof. exact (eq_refl (y = x)). Qed.
Lemma lem3316620 {A : Type'} (x' : A) (y : A) (x : A) : ((term100 A x x') = (y = x)) = ((x' = x) = (y = x)).
Proof. exact (MK_COMB (@lem3316618 A x' x) (@lem3316619 A y x)). Qed.
Lemma lem3316621 {A : Type'} (x' : A) (y : A) (x : A) : ((term100 A x x') = (term100 A x y)) = ((x' = x) = (y = x)).
Proof. exact (TRANS (@lem3316615 A x' y x) (@lem3316620 A x' y x)). Qed.
Lemma lem3316622 {A : Type'} (x : A) (x' : A) (y : A) (h1 : x' = y) : (x' = x) = (y = x).
Proof. exact (EQ_MP (@lem3316621 A x' y x) (@lem3316612 A x x' y h1)). Qed.
Lemma lem3316623 {A : Type'} (x : A) (x' : A) (y : A) (h1 : x' = x) (h2 : x' = y) : y = x.
Proof. exact (EQ_MP (@lem3316622 A x x' y h2) (@lem3316439 A x' x h1)). Qed.
Lemma lem3316651 {A : Type'} : (term103 A) = (term103 A).
Proof. exact (eq_refl (term103 A)). Qed.
Lemma lem3316652 {A : Type'} (x : A) (x' : A) (y : A) (h1 : x' = x) (h2 : x' = y) : (term104 A y) = (term104 A x).
Proof. exact (MK_COMB (@lem3316651 A) (@lem3316623 A x x' y h1 h2)). Qed.
Lemma lem3316653 {A : Type'} (x : A) : (term104 A x) = (term98 A x).
Proof. exact (eq_refl (term104 A x)). Qed.
Lemma lem3316654 {A : Type'} (y : A) : (term105 A y) = (term105 A y).
Proof. exact (eq_refl (term105 A y)). Qed.
Lemma lem3316655 {A : Type'} (y : A) (x : A) : ((term104 A y) = (term104 A x)) = ((term104 A y) = (term98 A x)).
Proof. exact (MK_COMB (@lem3316654 A y) (@lem3316653 A x)). Qed.
Lemma lem3316656 {A : Type'} (y : A) : (term104 A y) = (term98 A y).
Proof. exact (eq_refl (term104 A y)). Qed.
Lemma lem3316657 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3316658 {A : Type'} (y : A) : (term105 A y) = (term106 A y).
Proof. exact (MK_COMB (@lem3316657) (@lem3316656 A y)). Qed.
Lemma lem3316659 {A : Type'} (x : A) : (term98 A x) = (term98 A x).
Proof. exact (eq_refl (term98 A x)). Qed.
Lemma lem3316660 {A : Type'} (y : A) (x : A) : ((term104 A y) = (term98 A x)) = ((term98 A y) = (term98 A x)).
Proof. exact (MK_COMB (@lem3316658 A y) (@lem3316659 A x)). Qed.
Lemma lem3316661 {A : Type'} (y : A) (x : A) : ((term104 A y) = (term104 A x)) = ((term98 A y) = (term98 A x)).
Proof. exact (TRANS (@lem3316655 A y x) (@lem3316660 A y x)). Qed.
Lemma lem3316662 {A : Type'} (x : A) (x' : A) (y : A) (h1 : x' = x) (h2 : x' = y) : (term98 A y) = (term98 A x).
Proof. exact (EQ_MP (@lem3316661 A y x) (@lem3316652 A x x' y h1 h2)). Qed.
Lemma lem3316663 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = x) (h3 : x' = y) : term98 A x.
Proof. exact (EQ_MP (@lem3316662 A x x' y h2 h3) (@lem3316610 A x s x' y h1 h3)). Qed.
Lemma lem3316705 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3316719 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') : term92 A s x'.
Proof. exact (h1). Qed.
Lemma lem3316748 {A : Type'} (y : A) : (term93 A y) = (term93 A y).
Proof. exact (eq_refl (term93 A y)). Qed.
Lemma lem3316749 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : (term94 A y x') = (term97 A y).
Proof. exact (MK_COMB (@lem3316748 A y) (@lem3316457 A x' y h1)). Qed.
Lemma lem3316750 {A : Type'} (y : A) : (term97 A y) = (term98 A y).
Proof. exact (eq_refl (term97 A y)). Qed.
Lemma lem3316751 {A : Type'} (y : A) (x' : A) : (term95 A y x') = (term95 A y x').
Proof. exact (eq_refl (term95 A y x')). Qed.
Lemma lem3316752 {A : Type'} (x' : A) (y : A) : ((term94 A y x') = (term97 A y)) = ((term94 A y x') = (term98 A y)).
Proof. exact (MK_COMB (@lem3316751 A y x') (@lem3316750 A y)). Qed.
Lemma lem3316753 {A : Type'} (x' : A) (y : A) : (term94 A y x') = (term23 A x' y).
Proof. exact (eq_refl (term94 A y x')). Qed.
Lemma lem3316754 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3316755 {A : Type'} (x' : A) (y : A) : (term95 A y x') = (term96 A x' y).
Proof. exact (MK_COMB (@lem3316754) (@lem3316753 A x' y)). Qed.
Lemma lem3316756 {A : Type'} (y : A) : (term98 A y) = (term98 A y).
Proof. exact (eq_refl (term98 A y)). Qed.
Lemma lem3316757 {A : Type'} (x' : A) (y : A) : ((term94 A y x') = (term98 A y)) = ((term23 A x' y) = (term98 A y)).
Proof. exact (MK_COMB (@lem3316755 A x' y) (@lem3316756 A y)). Qed.
Lemma lem3316758 {A : Type'} (x' : A) (y : A) : ((term94 A y x') = (term97 A y)) = ((term23 A x' y) = (term98 A y)).
Proof. exact (TRANS (@lem3316752 A x' y) (@lem3316757 A x' y)). Qed.
Lemma lem3316759 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : (term23 A x' y) = (term98 A y).
Proof. exact (EQ_MP (@lem3316758 A x' y) (@lem3316749 A x' y h1)). Qed.
Lemma lem3316801 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = y) : term98 A y.
Proof. exact (EQ_MP (@lem3316759 A x' y h2) (@lem3316453 A x s x' y h1)). Qed.
Lemma lem3316884 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term70 A x s x') : term92 A s x'.
Proof. exact (proj2 (@lem3316322 A x s x' h1)). Qed.
Lemma lem3316926 {A : Type'} (y : A) : (term93 A y) = (term93 A y).
Proof. exact (eq_refl (term93 A y)). Qed.
Lemma lem3316927 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : (term94 A y x') = (term97 A y).
Proof. exact (MK_COMB (@lem3316926 A y) (@lem3316475 A x' y h1)). Qed.
Lemma lem3316928 {A : Type'} (y : A) : (term97 A y) = (term98 A y).
Proof. exact (eq_refl (term97 A y)). Qed.
Lemma lem3316929 {A : Type'} (y : A) (x' : A) : (term95 A y x') = (term95 A y x').
Proof. exact (eq_refl (term95 A y x')). Qed.
Lemma lem3316930 {A : Type'} (x' : A) (y : A) : ((term94 A y x') = (term97 A y)) = ((term94 A y x') = (term98 A y)).
Proof. exact (MK_COMB (@lem3316929 A y x') (@lem3316928 A y)). Qed.
Lemma lem3316931 {A : Type'} (x' : A) (y : A) : (term94 A y x') = (term23 A x' y).
Proof. exact (eq_refl (term94 A y x')). Qed.
Lemma lem3316932 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3316933 {A : Type'} (x' : A) (y : A) : (term95 A y x') = (term96 A x' y).
Proof. exact (MK_COMB (@lem3316932) (@lem3316931 A x' y)). Qed.
Lemma lem3316934 {A : Type'} (y : A) : (term98 A y) = (term98 A y).
Proof. exact (eq_refl (term98 A y)). Qed.
Lemma lem3316935 {A : Type'} (x' : A) (y : A) : ((term94 A y x') = (term98 A y)) = ((term23 A x' y) = (term98 A y)).
Proof. exact (MK_COMB (@lem3316933 A x' y) (@lem3316934 A y)). Qed.
Lemma lem3316936 {A : Type'} (x' : A) (y : A) : ((term94 A y x') = (term97 A y)) = ((term23 A x' y) = (term98 A y)).
Proof. exact (TRANS (@lem3316930 A x' y) (@lem3316935 A x' y)). Qed.
Lemma lem3316937 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : (term23 A x' y) = (term98 A y).
Proof. exact (EQ_MP (@lem3316936 A x' y) (@lem3316927 A x' y h1)). Qed.
Lemma lem3316980 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term84 A x s x' y) (h2 : x' = y) : term98 A y.
Proof. exact (EQ_MP (@lem3316937 A x' y h2) (@lem3316473 A x s x' y h1)). Qed.
Lemma lem3316996 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3316997 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3316996 A x). Qed.
Lemma lem3316998 {A : Type'} (y : A) : y = y.
Proof. exact (@lem3316997 A y). Qed.
Lemma lem3316999 {A : Type'} (y : A) : term107 A y.
Proof. exact (fun h0 : term98 A y => @lem3316998 A y). Qed.
Lemma lem3317001 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3317002 {A : Type'} (y : A) : (term107 A y) = (y = y).
Proof. exact (@lem3317001 (y = y)). Qed.
Lemma lem3317003 {A : Type'} (y : A) : y = y.
Proof. exact (EQ_MP (@lem3317002 A y) (@lem3316999 A y)). Qed.
Lemma lem3317006 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3317008 {A : Type'} (y : A) : (term98 A y) = (term109 A y).
Proof. exact (@lem3317006 (y = y)). Qed.
Lemma lem3317011 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term87 A x s x' y) (h2 : x = y) (h3 : x' = x) : term109 A y.
Proof. exact (EQ_MP (@lem3317008 A y) (@lem3316556 A s y x' x h1 h2 h3)). Qed.
Lemma lem3317014 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term87 A x s x' y) (h2 : x = y) (h3 : x' = x) : False.
Proof. exact (@lem3317011 A s y x' x h1 h2 h3 (@lem3317003 A y)). Qed.
Lemma lem3317015 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term87 A x s x' y) (h2 : x = y) (h3 : x' = x) : term110.
Proof. exact (fun h0 : ~ False => @lem3317014 A s y x' x h1 h2 h3). Qed.
Lemma lem3317017 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3317018 : term110 = False.
Proof. exact (@lem3317017 False). Qed.
Lemma lem3317023 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3317024 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3317023 A x). Qed.
Lemma lem3317025 {A : Type'} (x : A) : term107 A x.
Proof. exact (fun h0 : term98 A x => @lem3317024 A x). Qed.
Lemma lem3317027 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3317028 {A : Type'} (x : A) : (term107 A x) = (x = x).
Proof. exact (@lem3317027 (x = x)). Qed.
Lemma lem3317029 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3317028 A x) (@lem3317025 A x)). Qed.
Lemma lem3317032 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3317034 {A : Type'} (x : A) : (term98 A x) = (term109 A x).
Proof. exact (@lem3317032 (x = x)). Qed.
Lemma lem3317037 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = x) (h3 : x' = y) : term109 A x.
Proof. exact (EQ_MP (@lem3317034 A x) (@lem3316663 A s x x' y h1 h2 h3)). Qed.
Lemma lem3317040 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = x) (h3 : x' = y) : False.
Proof. exact (@lem3317037 A s x x' y h1 h2 h3 (@lem3317029 A x)). Qed.
Lemma lem3317041 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = x) (h3 : x' = y) : term110.
Proof. exact (fun h0 : ~ False => @lem3317040 A s x x' y h1 h2 h3). Qed.
Lemma lem3317043 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3317044 : term110 = False.
Proof. exact (@lem3317043 False). Qed.
Lemma lem3317061 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3317062 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term111 A s x'.
Proof. exact (fun h0 : term92 A s x' => @lem3317061 A s x' h1). Qed.
Lemma lem3317064 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3317065 {A : Type'} (s : A -> Prop) (x' : A) : (term111 A s x') = (s x').
Proof. exact (@lem3317064 (s x')). Qed.
Lemma lem3317066 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3317065 A s x') (@lem3317062 A s x' h1)). Qed.
Lemma lem3317069 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3317071 {A : Type'} (s : A -> Prop) (x' : A) : (term92 A s x') = (term112 A s x').
Proof. exact (@lem3317069 (s x')). Qed.
Lemma lem3317074 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') : term112 A s x'.
Proof. exact (EQ_MP (@lem3317071 A s x') (@lem3316719 A s x' h1)). Qed.
Lemma lem3317077 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : False.
Proof. exact (@lem3317074 A s x' h1 (@lem3317066 A s x' h2)). Qed.
Lemma lem3317078 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : term110.
Proof. exact (fun h0 : ~ False => @lem3317077 A s x' h1 h2). Qed.
Lemma lem3317080 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3317081 : term110 = False.
Proof. exact (@lem3317080 False). Qed.
Lemma lem3317082 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3317081) (@lem3317078 A s x' h1 h2)). Qed.
Lemma lem3317098 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3317099 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3317098 A x). Qed.
Lemma lem3317100 {A : Type'} (y : A) : y = y.
Proof. exact (@lem3317099 A y). Qed.
Lemma lem3317101 {A : Type'} (y : A) : term107 A y.
Proof. exact (fun h0 : term98 A y => @lem3317100 A y). Qed.
Lemma lem3317103 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3317104 {A : Type'} (y : A) : (term107 A y) = (y = y).
Proof. exact (@lem3317103 (y = y)). Qed.
Lemma lem3317105 {A : Type'} (y : A) : y = y.
Proof. exact (EQ_MP (@lem3317104 A y) (@lem3317101 A y)). Qed.
Lemma lem3317108 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3317110 {A : Type'} (y : A) : (term98 A y) = (term109 A y).
Proof. exact (@lem3317108 (y = y)). Qed.
Lemma lem3317113 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = y) : term109 A y.
Proof. exact (EQ_MP (@lem3317110 A y) (@lem3316801 A x s x' y h1 h2)). Qed.
Lemma lem3317116 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = y) : False.
Proof. exact (@lem3317113 A x s x' y h1 h2 (@lem3317105 A y)). Qed.
Lemma lem3317117 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = y) : term110.
Proof. exact (fun h0 : ~ False => @lem3317116 A x s x' y h1 h2). Qed.
Lemma lem3317119 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3317120 : term110 = False.
Proof. exact (@lem3317119 False). Qed.
Lemma lem3317137 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term84 A x s x' y) : s x'.
Proof. exact (proj1 (@lem3316318 A x s x' y h1)). Qed.
Lemma lem3317138 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term84 A x s x' y) : term111 A s x'.
Proof. exact (fun h0 : term92 A s x' => @lem3317137 A x s x' y h1). Qed.
Lemma lem3317140 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3317141 {A : Type'} (s : A -> Prop) (x' : A) : (term111 A s x') = (s x').
Proof. exact (@lem3317140 (s x')). Qed.
Lemma lem3317142 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term84 A x s x' y) : s x'.
Proof. exact (EQ_MP (@lem3317141 A s x') (@lem3317138 A x s x' y h1)). Qed.
Lemma lem3317145 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3317147 {A : Type'} (s : A -> Prop) (x' : A) : (term92 A s x') = (term112 A s x').
Proof. exact (@lem3317145 (s x')). Qed.
Lemma lem3317150 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term70 A x s x') : term112 A s x'.
Proof. exact (EQ_MP (@lem3317147 A s x') (@lem3316884 A x s x' h1)). Qed.
Lemma lem3317153 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term70 A x s x') (h2 : term84 A x s x' y) : False.
Proof. exact (@lem3317150 A x s x' h1 (@lem3317142 A x s x' y h2)). Qed.
Lemma lem3317154 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term70 A x s x') (h2 : term84 A x s x' y) : term110.
Proof. exact (fun h0 : ~ False => @lem3317153 A x s x' y h1 h2). Qed.
Lemma lem3317156 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3317157 : term110 = False.
Proof. exact (@lem3317156 False). Qed.
Lemma lem3317174 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3317175 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3317174 A x). Qed.
Lemma lem3317176 {A : Type'} (y : A) : y = y.
Proof. exact (@lem3317175 A y). Qed.
Lemma lem3317177 {A : Type'} (y : A) : term107 A y.
Proof. exact (fun h0 : term98 A y => @lem3317176 A y). Qed.
Lemma lem3317179 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3317180 {A : Type'} (y : A) : (term107 A y) = (y = y).
Proof. exact (@lem3317179 (y = y)). Qed.
Lemma lem3317181 {A : Type'} (y : A) : y = y.
Proof. exact (EQ_MP (@lem3317180 A y) (@lem3317177 A y)). Qed.
Lemma lem3317184 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3317186 {A : Type'} (y : A) : (term98 A y) = (term109 A y).
Proof. exact (@lem3317184 (y = y)). Qed.
Lemma lem3317189 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term84 A x s x' y) (h2 : x' = y) : term109 A y.
Proof. exact (EQ_MP (@lem3317186 A y) (@lem3316980 A x s x' y h1 h2)). Qed.
Lemma lem3317192 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term84 A x s x' y) (h2 : x' = y) : False.
Proof. exact (@lem3317189 A x s x' y h1 h2 (@lem3317181 A y)). Qed.
Lemma lem3317193 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term84 A x s x' y) (h2 : x' = y) : term110.
Proof. exact (fun h0 : ~ False => @lem3317192 A x s x' y h1 h2). Qed.
Lemma lem3317195 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3317196 : term110 = False.
Proof. exact (@lem3317195 False). Qed.
Lemma lem3317199 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term84 A x s x' y) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3317196) (@lem3317193 A x s x' y h1 h2)). Qed.
Lemma lem3317200 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term70 A x s x') (h2 : term84 A x s x' y) : False.
Proof. exact (EQ_MP (@lem3317157) (@lem3317154 A x s x' y h1 h2)). Qed.
Lemma lem3317202 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3317120) (@lem3317117 A x s x' y h1 h2)). Qed.
Lemma lem3317203 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : (term92 A s x') = False.
Proof. exact (prop_ext (fun h3 : term92 A s x' => @lem3317082 A s x' h1 h2) (fun h3 : False => @lem3316719 A s x' h1)). Qed.
Lemma lem3317204 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3317203 A s x' h1 h2) (@lem3316719 A s x' h1)). Qed.
Lemma lem3317205 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3317204 A s x' h1 h2) (fun h3 : False => @lem3316705 A s x' h2)). Qed.
Lemma lem3317207 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3317205 A s x' h1 h2) (@lem3316705 A s x' h2)). Qed.
Lemma lem3317209 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = x) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem3317044) (@lem3317041 A s x x' y h1 h2 h3)). Qed.
Lemma lem3317210 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term87 A x s x' y) (h2 : x = y) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3317018) (@lem3317015 A s y x' x h1 h2 h3)). Qed.
Lemma lem3317211 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term87 A x s x' y) (h2 : x = y) (h3 : x' = x) : (x = y) = False.
Proof. exact (prop_ext (fun h4 : x = y => @lem3317210 A s y x' x h1 h2 h3) (fun h4 : False => @lem3316503 A x y h2)). Qed.
Lemma lem3317213 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term87 A x s x' y) (h2 : x = y) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3317211 A s y x' x h1 h2 h3) (@lem3316503 A x y h2)). Qed.
Lemma lem3317214 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term84 A x s x' y) (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3317199 A x s x' y h1 h2) (fun h3 : False => @lem3316475 A x' y h2)). Qed.
Lemma lem3317215 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term84 A x s x' y) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3317214 A x s x' y h1 h2) (@lem3316475 A x' y h2)). Qed.
Lemma lem3317216 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3317202 A x s x' y h1 h2) (fun h3 : False => @lem3316457 A x' y h2)). Qed.
Lemma lem3317217 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3317216 A x s x' y h1 h2) (@lem3316457 A x' y h2)). Qed.
Lemma lem3317218 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : (term92 A s x') = False.
Proof. exact (prop_ext (fun h3 : term92 A s x' => @lem3317207 A s x' h1 h2) (fun h3 : False => @lem3316449 A s x' h1)). Qed.
Lemma lem3317219 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3317218 A s x' h1 h2) (@lem3316449 A s x' h1)). Qed.
Lemma lem3317220 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3317219 A s x' h1 h2) (fun h3 : False => @lem3316447 A s x' h2)). Qed.
Lemma lem3317221 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3317220 A s x' h1 h2) (@lem3316447 A s x' h2)). Qed.
Lemma lem3317222 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = x) (h3 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h4 : x' = y => @lem3317209 A s x x' y h1 h2 h3) (fun h4 : False => @lem3316441 A x' y h3)). Qed.
Lemma lem3317223 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = x) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem3317222 A s x x' y h1 h2 h3) (@lem3316441 A x' y h3)). Qed.
Lemma lem3317224 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = x) (h3 : x' = y) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3317223 A s x x' y h1 h2 h3) (fun h4 : False => @lem3316439 A x' x h2)). Qed.
Lemma lem3317225 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = x) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem3317224 A s x x' y h1 h2 h3) (@lem3316439 A x' x h2)). Qed.
Lemma lem3317226 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term87 A x s x' y) (h2 : x = y) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3317213 A s y x' x h1 h2 h3) (fun h4 : False => @lem3316431 A x' x h3)). Qed.
Lemma lem3317227 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term87 A x s x' y) (h2 : x = y) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3317226 A s y x' x h1 h2 h3) (@lem3316431 A x' x h3)). Qed.
Lemma lem3317228 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term87 A x s x' y) (h2 : x = y) (h3 : x' = x) : (x = y) = False.
Proof. exact (prop_ext (fun h4 : x = y => @lem3317227 A s y x' x h1 h2 h3) (fun h4 : False => @lem3316427 A x y h2)). Qed.
Lemma lem3317229 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term87 A x s x' y) (h2 : x = y) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3317228 A s y x' x h1 h2 h3) (@lem3316427 A x y h2)). Qed.
Lemma lem3317230 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term84 A x s x' y) (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3317215 A x s x' y h1 h2) (fun h3 : False => @lem3316425 A x' y h2)). Qed.
Lemma lem3317231 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term84 A x s x' y) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3317230 A x s x' y h1 h2) (@lem3316425 A x' y h2)). Qed.
Lemma lem3317232 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3317217 A x s x' y h1 h2) (fun h3 : False => @lem3316389 A x' y h2)). Qed.
Lemma lem3317233 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3317232 A x s x' y h1 h2) (@lem3316389 A x' y h2)). Qed.
Lemma lem3317234 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : (term92 A s x') = False.
Proof. exact (prop_ext (fun h3 : term92 A s x' => @lem3317221 A s x' h1 h2) (fun h3 : False => @lem3316373 A s x' h1)). Qed.
Lemma lem3317235 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3317234 A s x' h1 h2) (@lem3316373 A s x' h1)). Qed.
Lemma lem3317236 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3317235 A s x' h1 h2) (fun h3 : False => @lem3316369 A s x' h2)). Qed.
Lemma lem3317237 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3317236 A s x' h1 h2) (@lem3316369 A s x' h2)). Qed.
Lemma lem3317238 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = x) (h3 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h4 : x' = y => @lem3317225 A s x x' y h1 h2 h3) (fun h4 : False => @lem3316357 A x' y h3)). Qed.
Lemma lem3317239 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = x) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem3317238 A s x x' y h1 h2 h3) (@lem3316357 A x' y h3)). Qed.
Lemma lem3317240 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = x) (h3 : x' = y) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3317239 A s x x' y h1 h2 h3) (fun h4 : False => @lem3316353 A x' x h2)). Qed.
Lemma lem3317241 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = x) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem3317240 A s x x' y h1 h2 h3) (@lem3316353 A x' x h2)). Qed.
Lemma lem3317242 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term87 A x s x' y) (h2 : x = y) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3317229 A s y x' x h1 h2 h3) (fun h4 : False => @lem3316337 A x' x h3)). Qed.
Lemma lem3317243 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term87 A x s x' y) (h2 : x = y) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3317242 A s y x' x h1 h2 h3) (@lem3316337 A x' x h3)). Qed.
Lemma lem3317244 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term87 A x s x' y) (h2 : x = y) (h3 : x' = x) : (x = y) = False.
Proof. exact (prop_ext (fun h4 : x = y => @lem3317243 A s y x' x h1 h2 h3) (fun h4 : False => @lem3316329 A x y h2)). Qed.
Lemma lem3317245 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term87 A x s x' y) (h2 : x = y) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3317244 A s y x' x h1 h2 h3) (@lem3316329 A x y h2)). Qed.
Lemma lem3317246 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term84 A x s x' y) (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3317231 A x s x' y h1 h2) (fun h3 : False => @lem3316425 A x' y h2)). Qed.
Lemma lem3317247 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term84 A x s x' y) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3317246 A x s x' y h1 h2) (@lem3316425 A x' y h2)). Qed.
Lemma lem3317248 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3317233 A x s x' y h1 h2) (fun h3 : False => @lem3316389 A x' y h2)). Qed.
Lemma lem3317249 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3317248 A x s x' y h1 h2) (@lem3316389 A x' y h2)). Qed.
Lemma lem3317250 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : (term92 A s x') = False.
Proof. exact (prop_ext (fun h3 : term92 A s x' => @lem3317237 A s x' h1 h2) (fun h3 : False => @lem3316373 A s x' h1)). Qed.
Lemma lem3317251 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3317250 A s x' h1 h2) (@lem3316373 A s x' h1)). Qed.
Lemma lem3317252 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3317251 A s x' h1 h2) (fun h3 : False => @lem3316369 A s x' h2)). Qed.
Lemma lem3317253 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3317252 A s x' h1 h2) (@lem3316369 A s x' h2)). Qed.
Lemma lem3317254 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = x) (h3 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h4 : x' = y => @lem3317241 A s x x' y h1 h2 h3) (fun h4 : False => @lem3316357 A x' y h3)). Qed.
Lemma lem3317255 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = x) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem3317254 A s x x' y h1 h2 h3) (@lem3316357 A x' y h3)). Qed.
Lemma lem3317256 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = x) (h3 : x' = y) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3317255 A s x x' y h1 h2 h3) (fun h4 : False => @lem3316353 A x' x h2)). Qed.
Lemma lem3317257 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term87 A x s x' y) (h2 : x' = x) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem3317256 A s x x' y h1 h2 h3) (@lem3316353 A x' x h2)). Qed.
Lemma lem3317258 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term87 A x s x' y) (h2 : x = y) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3317245 A s y x' x h1 h2 h3) (fun h4 : False => @lem3316337 A x' x h3)). Qed.
Lemma lem3317259 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term87 A x s x' y) (h2 : x = y) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3317258 A s y x' x h1 h2 h3) (@lem3316337 A x' x h3)). Qed.
Lemma lem3317260 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term87 A x s x' y) (h2 : x = y) (h3 : x' = x) : (x = y) = False.
Proof. exact (prop_ext (fun h4 : x = y => @lem3317259 A s y x' x h1 h2 h3) (fun h4 : False => @lem3316329 A x y h2)). Qed.
Lemma lem3317261 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term87 A x s x' y) (h2 : x = y) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3317260 A s y x' x h1 h2 h3) (@lem3316329 A x y h2)). Qed.
Lemma lem3317262 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term84 A x s x' y) : False.
Proof. exact (or_elim (@lem3316319 A x s x' y h1) (fun h0 : term70 A x s x' => @lem3317200 A x s x' y h0 h1) (fun h0 : x' = y => @lem3317247 A x s x' y h1 h0)). Qed.
Lemma lem3317263 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : s x') (h2 : term87 A x s x' y) : False.
Proof. exact (or_elim (@lem3316308 A x s x' y h2) (fun h0 : term92 A s x' => @lem3317253 A s x' h0 h1) (fun h0 : x' = y => @lem3317249 A x s x' y h2 h0)). Qed.
Lemma lem3317264 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term87 A x s x' y) (h2 : x = y) (h3 : x' = x) : False.
Proof. exact (or_elim (@lem3316308 A x s x' y h1) (fun h0 : term92 A s x' => @lem3317261 A s y x' x h1 h2 h3) (fun h0 : x' = y => @lem3317257 A s x x' y h1 h3 h0)). Qed.
Lemma lem3317265 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (y : A) (h1 : term87 A x s x' y) (h2 : x = y) : False.
Proof. exact (or_elim (@lem3316311 A x s x' y h1) (fun h0 : x' = x => @lem3317264 A s y x' x h1 h2 h0) (fun h0 : s x' => @lem3317263 A x s x' y h0 h1)). Qed.
Lemma lem3317266 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (y : A) (h1 : term68 A x s x' y) (h2 : x = y) : False.
Proof. exact (or_elim (@lem3316305 A x s x' y h1) (fun h0 : term87 A x s x' y => @lem3317265 A s x' x y h0 h2) (fun h0 : term84 A x s x' y => @lem3317262 A x s x' y h0)). Qed.
Lemma lem3317267 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (y : A) (h1 : term68 A x s x' y) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem3317266 A s x' x y h1 h2) (fun h3 : False => @lem3316225 A x y h2)). Qed.
Lemma lem3317268 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (y : A) (h1 : term68 A x s x' y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3317267 A s x' x y h1 h2) (@lem3316225 A x y h2)). Qed.
Lemma lem3317269 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (y : A) (h1 : term68 A x s x' y) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem3317268 A s x' x y h1 h2) (fun h3 : False => @lem3316165 A x y h2)). Qed.
Lemma lem3317270 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (y : A) (h1 : term68 A x s x' y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3317269 A s x' x y h1 h2) (@lem3316165 A x y h2)). Qed.
Lemma lem3317271 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (y : A) (h1 : term68 A x s x' y) (h2 : x = y) : (term68 A x s x' y) = False.
Proof. exact (prop_ext (fun h3 : term68 A x s x' y => @lem3317270 A s x' x y h1 h2) (fun h3 : False => @lem3316159 A x s x' y h1)). Qed.
Lemma lem3317272 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (y : A) (h1 : term68 A x s x' y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3317271 A s x' x y h1 h2) (@lem3316159 A x s x' y h1)). Qed.
Lemma lem3317273 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (y : A) (h1 : x = y) : term67 A x s x' y.
Proof. exact (fun h0 : term68 A x s x' y => @lem3317272 A s x' x y h0 h1). Qed.
Lemma lem3317274 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (y : A) (h1 : x = y) : (term37 A x s x' y) = (term42 A s x' y).
Proof. exact (EQ_MP (@lem3316158 A x s x' y) (@lem3317273 A s x' x y h1)). Qed.
Lemma lem3317279 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : x = y) : term45 A x s y.
Proof. exact (fun x' : A => @lem3317274 A s x' x y h1). Qed.
Lemma lem3317280 {A : Type'} (x : A) (s : A -> Prop) (y : A) : term46 A x s y.
Proof. exact (fun h0 : x = y => @lem3317279 A s x y h0). Qed.
Lemma lem3317285 {A : Type'} (s : A -> Prop) (y : A) : term58 A s y.
Proof. exact (fun x : A => @lem3317280 A x s y). Qed.
Lemma lem3317290 {A : Type'} (y : A) : term62 A y.
Proof. exact (fun s : A -> Prop => @lem3317285 A s y). Qed.
Lemma lem3317295 {A : Type'} : term66 A.
Proof. exact (fun y : A => @lem3317290 A y). Qed.
Lemma lem3317296 {A : Type'} : term65 A.
Proof. exact (EQ_MP (@lem3316153 A) (@lem3317295 A)). Qed.
Lemma lem3317297 {A : Type'} (y : A) : term113 A y.
Proof. exact (@lem3317296 A y). Qed.
Lemma lem3317298 {A : Type'} (y : A) : (term113 A y) = (term61 A y).
Proof. exact (eq_refl (term113 A y)). Qed.
Lemma lem3317299 {A : Type'} (y : A) : term61 A y.
Proof. exact (EQ_MP (@lem3317298 A y) (@lem3317297 A y)). Qed.
Lemma lem3317300 {A : Type'} (y : A) (s : A -> Prop) : term114 A y s.
Proof. exact (@lem3317299 A y s). Qed.
Lemma lem3317301 {A : Type'} (s : A -> Prop) (y : A) : (term114 A y s) = (term57 A s y).
Proof. exact (eq_refl (term114 A y s)). Qed.
Lemma lem3317302 {A : Type'} (s : A -> Prop) (y : A) : term57 A s y.
Proof. exact (EQ_MP (@lem3317301 A s y) (@lem3317300 A y s)). Qed.
Lemma lem3317303 {A : Type'} (s : A -> Prop) (y : A) (x : A) : term115 A s y x.
Proof. exact (@lem3317302 A s y x). Qed.
Lemma lem3317304 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term115 A s y x) = (term48 A x s y).
Proof. exact (eq_refl (term115 A s y x)). Qed.
Lemma lem3317305 {A : Type'} (x : A) (s : A -> Prop) (y : A) : term48 A x s y.
Proof. exact (EQ_MP (@lem3317304 A x s y) (@lem3317303 A s y x)). Qed.
Lemma lem3317307 {A : Type'} (x : A) (s : A -> Prop) (y : A) : term48 A x s y.
Proof. exact (@lem3316024 A x s y (@lem3317305 A x s y)). Qed.
Lemma lem3317308 {A : Type'} (x : A) (s : A -> Prop) (y : A) (h1 : term49 A x s y) : False.
Proof. exact (@lem3317307 A x s y (@lem3316008 A x s y h1)). Qed.
Lemma lem3317309 {A : Type'} (x : A) (s : A -> Prop) (y : A) (h1 : term49 A x s y) : (term49 A x s y) = False.
Proof. exact (prop_ext (fun h2 : term49 A x s y => @lem3317308 A x s y h1) (fun h2 : False => @lem3316008 A x s y h1)). Qed.
Lemma lem3317310 {A : Type'} (x : A) (s : A -> Prop) (y : A) (h1 : term49 A x s y) : False.
Proof. exact (EQ_MP (@lem3317309 A x s y h1) (@lem3316008 A x s y h1)). Qed.
Lemma lem3317311 {A : Type'} (x : A) (s : A -> Prop) (y : A) : term48 A x s y.
Proof. exact (fun h0 : term49 A x s y => @lem3317310 A x s y h0). Qed.
Lemma lem3317312 {A : Type'} (x : A) (s : A -> Prop) (y : A) : term46 A x s y.
Proof. exact (EQ_MP (@lem3316007 A x s y) (@lem3317311 A x s y)). Qed.
Lemma lem3317313 {A : Type'} (x : A) (s : A -> Prop) (y : A) : term26 A x s y.
Proof. exact (EQ_MP (@lem3316003 A x s y) (@lem3317312 A x s y)). Qed.
Lemma lem3317314 {A : Type'} (x : A) (s : A -> Prop) (y : A) : term16 A x s y.
Proof. exact (EQ_MP (@lem3315921 A x s y) (@lem3317313 A x s y)). Qed.
Lemma lem3317324 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term24 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3317325 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term24 A s t).
Proof. exact (@lem3317324 A s t). Qed.
Lemma lem3317326 {A : Type'} (x : A) (s : A -> Prop) (y : A) : ((term9 A x s y) = (term7 A x s y)) = (term116 A x s y).
Proof. exact (@lem3317325 A (term9 A x s y) (term7 A x s y)). Qed.
Lemma lem3317335 {A : Type'} (x : A) (y : A) : (term10 A x y) = (term10 A x y).
Proof. exact (eq_refl (term10 A x y)). Qed.
Lemma lem3317336 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term12 A x s y) = (term117 A x s y).
Proof. exact (MK_COMB (@lem3317335 A x y) (@lem3317326 A x s y)). Qed.
Lemma lem3317339 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term117 A x s y) = (term12 A x s y).
Proof. exact (SYM (@lem3317336 A x s y)). Qed.
Lemma lem3317351 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term27 A x s y) = (term28 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3317352 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term27 A x s y) = (term28 A s x y).
Proof. exact (@lem3317351 A s x y). Qed.
Lemma lem3317353 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term29 A x' x s y) = (term30 A x s x' y).
Proof. exact (@lem3317352 A (@INSERT A x s) x' y). Qed.
Lemma lem3317357 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term31 A x y s) = (term32 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3317358 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term31 A x y s) = (term32 A y x s).
Proof. exact (@lem3317357 A y x s). Qed.
Lemma lem3317359 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term31 A x' x s) = (term32 A x x' s).
Proof. exact (@lem3317358 A x x' s). Qed.
Lemma lem3317365 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3317366 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3317365 A P x). Qed.
Lemma lem3317367 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3317366 A s x'). Qed.
Lemma lem3317368 {A : Type'} (x' : A) (x : A) : (term33 A x' x) = (term33 A x' x).
Proof. exact (eq_refl (term33 A x' x)). Qed.
Lemma lem3317369 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term32 A x x' s) = (term34 A x s x').
Proof. exact (MK_COMB (@lem3317368 A x' x) (@lem3317367 A s x')). Qed.
Lemma lem3317372 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term31 A x' x s) = (term34 A x s x').
Proof. exact (TRANS (@lem3317359 A x x' s) (@lem3317369 A x s x')). Qed.
Lemma lem3317373 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3317374 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term35 A x' x s) = (term36 A x s x').
Proof. exact (MK_COMB (@lem3317373) (@lem3317372 A x s x')). Qed.
Lemma lem3317377 {A : Type'} (x' : A) (y : A) : (term23 A x' y) = (term23 A x' y).
Proof. exact (eq_refl (term23 A x' y)). Qed.
Lemma lem3317378 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term30 A x s x' y) = (term37 A x s x' y).
Proof. exact (MK_COMB (@lem3317374 A x s x') (@lem3317377 A x' y)). Qed.
Lemma lem3317381 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term29 A x' x s y) = (term37 A x s x' y).
Proof. exact (TRANS (@lem3317353 A x s x' y) (@lem3317378 A x s x' y)). Qed.
Lemma lem3317382 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3317383 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term38 A x' x s y) = (term39 A x s x' y).
Proof. exact (MK_COMB (@lem3317382) (@lem3317381 A x s x' y)). Qed.
Lemma lem3317385 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term31 A x y s) = (term32 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3317386 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term31 A x y s) = (term32 A y x s).
Proof. exact (@lem3317385 A y x s). Qed.
Lemma lem3317387 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (y : A) : (term118 A x' x s y) = (term119 A x x' s y).
Proof. exact (@lem3317386 A x x' (@DELETE A s y)). Qed.
Lemma lem3317393 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term27 A x s y) = (term28 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3317394 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term27 A x s y) = (term28 A s x y).
Proof. exact (@lem3317393 A s x y). Qed.
Lemma lem3317395 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term27 A x' s y) = (term28 A s x' y).
Proof. exact (@lem3317394 A s x' y). Qed.
Lemma lem3317399 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3317400 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3317399 A P x). Qed.
Lemma lem3317401 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3317400 A s x'). Qed.
Lemma lem3317402 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3317403 {A : Type'} (s : A -> Prop) (x' : A) : (term40 A x' s) = (term41 A s x').
Proof. exact (MK_COMB (@lem3317402) (@lem3317401 A s x')). Qed.
Lemma lem3317406 {A : Type'} (x' : A) (y : A) : (term23 A x' y) = (term23 A x' y).
Proof. exact (eq_refl (term23 A x' y)). Qed.
Lemma lem3317407 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term28 A s x' y) = (term42 A s x' y).
Proof. exact (MK_COMB (@lem3317403 A s x') (@lem3317406 A x' y)). Qed.
Lemma lem3317410 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term27 A x' s y) = (term42 A s x' y).
Proof. exact (TRANS (@lem3317395 A s x' y) (@lem3317407 A s x' y)). Qed.
Lemma lem3317411 {A : Type'} (x' : A) (x : A) : (term33 A x' x) = (term33 A x' x).
Proof. exact (eq_refl (term33 A x' x)). Qed.
Lemma lem3317412 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term119 A x x' s y) = (term120 A x s x' y).
Proof. exact (MK_COMB (@lem3317411 A x' x) (@lem3317410 A s x' y)). Qed.
Lemma lem3317415 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term118 A x' x s y) = (term120 A x s x' y).
Proof. exact (TRANS (@lem3317387 A x x' s y) (@lem3317412 A x s x' y)). Qed.
Lemma lem3317416 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : ((term29 A x' x s y) = (term118 A x' x s y)) = ((term37 A x s x' y) = (term120 A x s x' y)).
Proof. exact (MK_COMB (@lem3317383 A x s x' y) (@lem3317415 A x s x' y)). Qed.
Lemma lem3317419 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term121 A x s y) = (term122 A x s y).
Proof. exact (fun_ext (fun x' : A => @lem3317416 A x s x' y)). Qed.
Lemma lem3317420 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3317421 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term116 A x s y) = (term123 A x s y).
Proof. exact (MK_COMB (@lem3317420 A) (@lem3317419 A x s y)). Qed.
Lemma lem3317426 {A : Type'} (x : A) (y : A) : (term10 A x y) = (term10 A x y).
Proof. exact (eq_refl (term10 A x y)). Qed.
Lemma lem3317427 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term117 A x s y) = (term124 A x s y).
Proof. exact (MK_COMB (@lem3317426 A x y) (@lem3317421 A x s y)). Qed.
Lemma lem3317430 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term124 A x s y) = (term117 A x s y).
Proof. exact (SYM (@lem3317427 A x s y)). Qed.
Lemma lem3317432 (p : Prop) : p = (term47 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3317433 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term124 A x s y) = (term125 A x s y).
Proof. exact (@lem3317432 (term124 A x s y)). Qed.
Lemma lem3317434 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term125 A x s y) = (term124 A x s y).
Proof. exact (SYM (@lem3317433 A x s y)). Qed.
Lemma lem3317435 {A : Type'} (x : A) (s : A -> Prop) (y : A) (h1 : term126 A x s y) : term126 A x s y.
Proof. exact (h1). Qed.
Lemma lem3317438 {A : Type'} (x : A) (s : A -> Prop) (y : A) (h1 : term125 A x s y) : term125 A x s y.
Proof. exact (h1). Qed.
Lemma lem3317439 {A : Type'} (x : A) (s : A -> Prop) (y : A) : term127 A x s y.
Proof. exact (fun h0 : term125 A x s y => @lem3317438 A x s y h0). Qed.
Lemma lem3317440 {A : Type'} (x : A) (s : A -> Prop) (y : A) (h1 : term127 A x s y) : term127 A x s y.
Proof. exact (h1). Qed.
Lemma lem3317441 {A : Type'} (x : A) (s : A -> Prop) (y : A) (h1 : term125 A x s y) : term125 A x s y.
Proof. exact (h1). Qed.
Lemma lem3317442 {A : Type'} (x : A) (s : A -> Prop) (y : A) (h1 : term125 A x s y) (h2 : term127 A x s y) : term125 A x s y.
Proof. exact (@lem3317440 A x s y h2 (@lem3317441 A x s y h1)). Qed.
Lemma lem3317443 {A : Type'} (x : A) (s : A -> Prop) (y : A) (h1 : term125 A x s y) : term128 A x s y.
Proof. exact (fun h0 : term127 A x s y => @lem3317442 A x s y h1 h0). Qed.
Lemma lem3317444 {A : Type'} (x : A) (s : A -> Prop) (y : A) (h1 : term127 A x s y) : term127 A x s y.
Proof. exact (h1). Qed.
Lemma lem3317445 {A : Type'} (x : A) (s : A -> Prop) (y : A) (h1 : term125 A x s y) (h2 : term127 A x s y) : term125 A x s y.
Proof. exact (@lem3317443 A x s y h1 (@lem3317444 A x s y h2)). Qed.
Lemma lem3317446 {A : Type'} (x : A) (s : A -> Prop) (y : A) (h1 : term127 A x s y) : term127 A x s y.
Proof. exact (fun h0 : term125 A x s y => @lem3317445 A x s y h0 h1). Qed.
Lemma lem3317447 {A : Type'} (x : A) (s : A -> Prop) (y : A) : term129 A x s y.
Proof. exact (fun h0 : term127 A x s y => @lem3317446 A x s y h0). Qed.
Lemma lem3317450 {A : Type'} (x : A) (s : A -> Prop) (y : A) : term127 A x s y.
Proof. exact (@lem3317447 A x s y (@lem3317439 A x s y)). Qed.
Lemma lem3317451 {A : Type'} (x : A) (s : A -> Prop) (y : A) : term127 A x s y.
Proof. exact (@lem3317450 A x s y). Qed.
Lemma lem3317465 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3317466 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term125 A x s y) = (term130 A x s y).
Proof. exact (@lem3317465 (term126 A x s y)). Qed.
Lemma lem3317468 (t : Prop) : (term54 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3317469 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term130 A x s y) = (term124 A x s y).
Proof. exact (@lem3317468 (term124 A x s y)). Qed.
Lemma lem3317472 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term125 A x s y) = (term124 A x s y).
Proof. exact (TRANS (@lem3317466 A x s y) (@lem3317469 A x s y)). Qed.
Lemma lem3317485 {A : Type'} (s : A -> Prop) (y : A) : (term131 A s y) = (term132 A s y).
Proof. exact (fun_ext (fun x : A => @lem3317472 A x s y)). Qed.
Lemma lem3317486 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3317487 {A : Type'} (s : A -> Prop) (y : A) : (term133 A s y) = (term134 A s y).
Proof. exact (MK_COMB (@lem3317486 A) (@lem3317485 A s y)). Qed.
Lemma lem3317492 {A : Type'} (y : A) : (term135 A y) = (term136 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3317487 A s y)). Qed.
Lemma lem3317493 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3317494 {A : Type'} (y : A) : (term137 A y) = (term138 A y).
Proof. exact (MK_COMB (@lem3317493 A) (@lem3317492 A y)). Qed.
Lemma lem3317499 {A : Type'} : (term139 A) = (term140 A).
Proof. exact (fun_ext (fun y : A => @lem3317494 A y)). Qed.
Lemma lem3317500 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3317509 {A : Type'} : (term141 A) = (term142 A).
Proof. exact (MK_COMB (@lem3317500 A) (@lem3317499 A)). Qed.
Lemma lem3317534 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : ((term37 A x s x' y) = (term120 A x s x' y)) = ((term37 A x s x' y) = (term120 A x s x' y)).
Proof. exact (eq_refl ((term37 A x s x' y) = (term120 A x s x' y))). Qed.
Lemma lem3317535 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term122 A x s y) = (term122 A x s y).
Proof. exact (fun_ext (fun x' : A => @lem3317534 A x s x' y)). Qed.
Lemma lem3317536 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3317537 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term123 A x s y) = (term123 A x s y).
Proof. exact (MK_COMB (@lem3317536 A) (@lem3317535 A x s y)). Qed.
Lemma lem3317542 {A : Type'} (x : A) (y : A) : (term10 A x y) = (term10 A x y).
Proof. exact (eq_refl (term10 A x y)). Qed.
Lemma lem3317543 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term124 A x s y) = (term124 A x s y).
Proof. exact (MK_COMB (@lem3317542 A x y) (@lem3317537 A x s y)). Qed.
Lemma lem3317544 {A : Type'} (s : A -> Prop) (y : A) : (term132 A s y) = (term132 A s y).
Proof. exact (fun_ext (fun x : A => @lem3317543 A x s y)). Qed.
Lemma lem3317545 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3317546 {A : Type'} (s : A -> Prop) (y : A) : (term134 A s y) = (term134 A s y).
Proof. exact (MK_COMB (@lem3317545 A) (@lem3317544 A s y)). Qed.
Lemma lem3317547 {A : Type'} (y : A) : (term136 A y) = (term136 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3317546 A s y)). Qed.
Lemma lem3317548 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3317549 {A : Type'} (y : A) : (term138 A y) = (term138 A y).
Proof. exact (MK_COMB (@lem3317548 A) (@lem3317547 A y)). Qed.
Lemma lem3317550 {A : Type'} : (term140 A) = (term140 A).
Proof. exact (fun_ext (fun y : A => @lem3317549 A y)). Qed.
Lemma lem3317551 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3317552 {A : Type'} : (term142 A) = (term142 A).
Proof. exact (MK_COMB (@lem3317551 A) (@lem3317550 A)). Qed.
Lemma lem3317589 {A : Type'} : (term141 A) = (term142 A).
Proof. exact (TRANS (@lem3317509 A) (@lem3317552 A)). Qed.
Lemma lem3317590 {A : Type'} : (term142 A) = (term141 A).
Proof. exact (SYM (@lem3317589 A)). Qed.
Lemma lem3317593 (p : Prop) : p = (term47 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3317594 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : ((term37 A x s x' y) = (term120 A x s x' y)) = (term143 A x s x' y).
Proof. exact (@lem3317593 ((term37 A x s x' y) = (term120 A x s x' y))). Qed.
Lemma lem3317595 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term143 A x s x' y) = ((term37 A x s x' y) = (term120 A x s x' y)).
Proof. exact (SYM (@lem3317594 A x s x' y)). Qed.
Lemma lem3317596 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term144 A x s x' y) : term144 A x s x' y.
Proof. exact (h1). Qed.
Lemma lem3317602 {A : Type'} (x : A) (y : A) (h1 : term23 A x y) : term23 A x y.
Proof. exact (h1). Qed.
Lemma lem3317611 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term69 A x s x') = (term70 A x s x').
Proof. exact (@lem17160 (x' = x) (s x')). Qed.
Lemma lem3317618 {A : Type'} (x' : A) (y : A) : (term71 A x' y) = (x' = y).
Proof. exact (@lem16933 (x' = y)). Qed.
Lemma lem3317619 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3317620 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term72 A x s x') = (term73 A x s x').
Proof. exact (MK_COMB (@lem3317619) (@lem3317611 A x s x')). Qed.
Lemma lem3317621 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term74 A x s x' y) = (term75 A x s x' y).
Proof. exact (MK_COMB (@lem3317620 A x s x') (@lem3317618 A x' y)). Qed.
Lemma lem3317622 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term76 A x s x' y) = (term74 A x s x' y).
Proof. exact (@lem17045 (term34 A x s x') (term23 A x' y)). Qed.
Lemma lem3317623 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term76 A x s x' y) = (term75 A x s x' y).
Proof. exact (TRANS (@lem3317622 A x s x' y) (@lem3317621 A x s x' y)). Qed.
Lemma lem3317634 {A : Type'} (x' : A) (y : A) : (term71 A x' y) = (x' = y).
Proof. exact (@lem16933 (x' = y)). Qed.
Lemma lem3317636 {A : Type'} (s : A -> Prop) (x' : A) : (term77 A s x') = (term77 A s x').
Proof. exact (eq_refl (term77 A s x')). Qed.
Lemma lem3317637 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term78 A s x' y) = (term79 A s x' y).
Proof. exact (MK_COMB (@lem3317636 A s x') (@lem3317634 A x' y)). Qed.
Lemma lem3317638 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term80 A s x' y) = (term78 A s x' y).
Proof. exact (@lem17045 (s x') (term23 A x' y)). Qed.
Lemma lem3317639 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term80 A s x' y) = (term79 A s x' y).
Proof. exact (TRANS (@lem3317638 A s x' y) (@lem3317637 A s x' y)). Qed.
Lemma lem3317644 {A : Type'} (x' : A) (x : A) : (term145 A x' x) = (term145 A x' x).
Proof. exact (eq_refl (term145 A x' x)). Qed.
Lemma lem3317645 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term146 A x s x' y) = (term147 A x s x' y).
Proof. exact (MK_COMB (@lem3317644 A x' x) (@lem3317639 A s x' y)). Qed.
Lemma lem3317646 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term148 A x s x' y) = (term146 A x s x' y).
Proof. exact (@lem17160 (x' = x) (term42 A s x' y)). Qed.
Lemma lem3317647 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term148 A x s x' y) = (term147 A x s x' y).
Proof. exact (TRANS (@lem3317646 A x s x' y) (@lem3317645 A x s x' y)). Qed.
Lemma lem3317650 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term120 A x s x' y) = (term120 A x s x' y).
Proof. exact (eq_refl (term120 A x s x' y)). Qed.
Lemma lem3317651 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3317652 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term81 A x s x' y) = (term82 A x s x' y).
Proof. exact (MK_COMB (@lem3317651) (@lem3317623 A x s x' y)). Qed.
Lemma lem3317653 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term149 A x s x' y) = (term150 A x s x' y).
Proof. exact (MK_COMB (@lem3317652 A x s x' y) (@lem3317650 A x s x' y)). Qed.
Lemma lem3317655 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term85 A x s x' y) = (term85 A x s x' y).
Proof. exact (eq_refl (term85 A x s x' y)). Qed.
Lemma lem3317656 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term151 A x s x' y) = (term152 A x s x' y).
Proof. exact (MK_COMB (@lem3317655 A x s x' y) (@lem3317647 A x s x' y)). Qed.
Lemma lem3317657 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3317658 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term153 A x s x' y) = (term154 A x s x' y).
Proof. exact (MK_COMB (@lem3317657) (@lem3317656 A x s x' y)). Qed.
Lemma lem3317659 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term155 A x s x' y) = (term156 A x s x' y).
Proof. exact (MK_COMB (@lem3317658 A x s x' y) (@lem3317653 A x s x' y)). Qed.
Lemma lem3317660 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term144 A x s x' y) = (term155 A x s x' y).
Proof. exact (@lem17646 (term37 A x s x' y) (term120 A x s x' y)). Qed.
Lemma lem3317665 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) : (term144 A x s x' y) = (term156 A x s x' y).
Proof. exact (TRANS (@lem3317660 A x s x' y) (@lem3317659 A x s x' y)). Qed.
Lemma lem3317674 {A : Type'} (x : A) (y : A) (h1 : term23 A x y) : term23 A x y.
Proof. exact (h1). Qed.
Lemma lem3317772 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term144 A x s x' y) : term156 A x s x' y.
Proof. exact (EQ_MP (@lem3317665 A x s x' y) (@lem3317596 A x s x' y h1)). Qed.
Lemma lem3317773 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term152 A x s x' y) : term152 A x s x' y.
Proof. exact (h1). Qed.
Lemma lem3317774 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term150 A x s x' y) : term150 A x s x' y.
Proof. exact (h1). Qed.
Lemma lem3317775 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term152 A x s x' y) : term147 A x s x' y.
Proof. exact (proj2 (@lem3317773 A x s x' y h1)). Qed.
Lemma lem3317776 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term152 A x s x' y) : term37 A x s x' y.
Proof. exact (proj1 (@lem3317773 A x s x' y h1)). Qed.
Lemma lem3317777 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term152 A x s x' y) : term79 A s x' y.
Proof. exact (proj2 (@lem3317775 A x s x' y h1)). Qed.
Lemma lem3317780 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term152 A x s x' y) : term34 A x s x'.
Proof. exact (proj1 (@lem3317776 A x s x' y h1)). Qed.
Lemma lem3317787 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term150 A x s x' y) : term120 A x s x' y.
Proof. exact (proj2 (@lem3317774 A x s x' y h1)). Qed.
Lemma lem3317788 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term150 A x s x' y) : term75 A x s x' y.
Proof. exact (proj1 (@lem3317774 A x s x' y h1)). Qed.
Lemma lem3317790 {A : Type'} (s : A -> Prop) (x' : A) (y : A) (h1 : term42 A s x' y) : term42 A s x' y.
Proof. exact (h1). Qed.
Lemma lem3317791 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term70 A x s x') : term70 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3317797 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term70 A x s x') : term70 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3317816 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3317836 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3317840 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem3317856 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3317860 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') : term92 A s x'.
Proof. exact (h1). Qed.
Lemma lem3317880 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem3317888 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3317900 {A : Type'} (x : A) (y : A) (h1 : term23 A x y) : term23 A x y.
Proof. exact (h1). Qed.
Lemma lem3317904 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3317908 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem3317944 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem3317948 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term152 A x s x' y) : term23 A x' x.
Proof. exact (proj1 (@lem3317775 A x s x' y h1)). Qed.
Lemma lem3317952 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3317958 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term152 A x s x' y) : term23 A x' x.
Proof. exact (proj1 (@lem3317775 A x s x' y h1)). Qed.
Lemma lem3317962 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3317964 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem3317972 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3317974 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') : term92 A s x'.
Proof. exact (h1). Qed.
Lemma lem3317980 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term152 A x s x' y) : term23 A x' y.
Proof. exact (proj2 (@lem3317776 A x s x' y h1)). Qed.
Lemma lem3317984 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem3317988 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3317990 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term70 A x s x') : term23 A x' x.
Proof. exact (proj1 (@lem3317791 A x s x' h1)). Qed.
Lemma lem3317994 {A : Type'} (x : A) (y : A) (h1 : term23 A x y) : term23 A x y.
Proof. exact (h1). Qed.
Lemma lem3317996 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3317998 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem3318008 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term70 A x s x') : term92 A s x'.
Proof. exact (proj2 (@lem3317797 A x s x' h1)). Qed.
Lemma lem3318014 {A : Type'} (s : A -> Prop) (x' : A) (y : A) (h1 : term42 A s x' y) : term23 A x' y.
Proof. exact (proj2 (@lem3317790 A s x' y h1)). Qed.
Lemma lem3318016 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem3318045 {A : Type'} (x : A) : (term93 A x) = (term93 A x).
Proof. exact (eq_refl (term93 A x)). Qed.
Lemma lem3318046 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term94 A x x') = (term97 A x).
Proof. exact (MK_COMB (@lem3318045 A x) (@lem3317952 A x' x h1)). Qed.
Lemma lem3318047 {A : Type'} (x : A) : (term97 A x) = (term98 A x).
Proof. exact (eq_refl (term97 A x)). Qed.
Lemma lem3318048 {A : Type'} (x : A) (x' : A) : (term95 A x x') = (term95 A x x').
Proof. exact (eq_refl (term95 A x x')). Qed.
Lemma lem3318049 {A : Type'} (x' : A) (x : A) : ((term94 A x x') = (term97 A x)) = ((term94 A x x') = (term98 A x)).
Proof. exact (MK_COMB (@lem3318048 A x x') (@lem3318047 A x)). Qed.
Lemma lem3318050 {A : Type'} (x' : A) (x : A) : (term94 A x x') = (term23 A x' x).
Proof. exact (eq_refl (term94 A x x')). Qed.
Lemma lem3318051 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3318052 {A : Type'} (x' : A) (x : A) : (term95 A x x') = (term96 A x' x).
Proof. exact (MK_COMB (@lem3318051) (@lem3318050 A x' x)). Qed.
Lemma lem3318053 {A : Type'} (x : A) : (term98 A x) = (term98 A x).
Proof. exact (eq_refl (term98 A x)). Qed.
Lemma lem3318054 {A : Type'} (x' : A) (x : A) : ((term94 A x x') = (term98 A x)) = ((term23 A x' x) = (term98 A x)).
Proof. exact (MK_COMB (@lem3318052 A x' x) (@lem3318053 A x)). Qed.
Lemma lem3318055 {A : Type'} (x' : A) (x : A) : ((term94 A x x') = (term97 A x)) = ((term23 A x' x) = (term98 A x)).
Proof. exact (TRANS (@lem3318049 A x' x) (@lem3318054 A x' x)). Qed.
Lemma lem3318056 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term23 A x' x) = (term98 A x).
Proof. exact (EQ_MP (@lem3318055 A x' x) (@lem3318046 A x' x h1)). Qed.
Lemma lem3318057 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term152 A x s x' y) (h2 : x' = x) : term98 A x.
Proof. exact (EQ_MP (@lem3318056 A x' x h2) (@lem3317948 A x s x' y h1)). Qed.
Lemma lem3318112 {A : Type'} (x : A) : (term93 A x) = (term93 A x).
Proof. exact (eq_refl (term93 A x)). Qed.
Lemma lem3318113 {A : Type'} (x : A) (x' : A) (y : A) (h1 : x' = y) : (term94 A x x') = (term94 A x y).
Proof. exact (MK_COMB (@lem3318112 A x) (@lem3317964 A x' y h1)). Qed.
Lemma lem3318114 {A : Type'} (y : A) (x : A) : (term94 A x y) = (term23 A y x).
Proof. exact (eq_refl (term94 A x y)). Qed.
Lemma lem3318115 {A : Type'} (x : A) (x' : A) : (term95 A x x') = (term95 A x x').
Proof. exact (eq_refl (term95 A x x')). Qed.
Lemma lem3318116 {A : Type'} (x' : A) (y : A) (x : A) : ((term94 A x x') = (term94 A x y)) = ((term94 A x x') = (term23 A y x)).
Proof. exact (MK_COMB (@lem3318115 A x x') (@lem3318114 A y x)). Qed.
Lemma lem3318117 {A : Type'} (x' : A) (x : A) : (term94 A x x') = (term23 A x' x).
Proof. exact (eq_refl (term94 A x x')). Qed.
Lemma lem3318118 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3318119 {A : Type'} (x' : A) (x : A) : (term95 A x x') = (term96 A x' x).
Proof. exact (MK_COMB (@lem3318118) (@lem3318117 A x' x)). Qed.
Lemma lem3318120 {A : Type'} (y : A) (x : A) : (term23 A y x) = (term23 A y x).
Proof. exact (eq_refl (term23 A y x)). Qed.
Lemma lem3318121 {A : Type'} (x' : A) (y : A) (x : A) : ((term94 A x x') = (term23 A y x)) = ((term23 A x' x) = (term23 A y x)).
Proof. exact (MK_COMB (@lem3318119 A x' x) (@lem3318120 A y x)). Qed.
Lemma lem3318122 {A : Type'} (x' : A) (y : A) (x : A) : ((term94 A x x') = (term94 A x y)) = ((term23 A x' x) = (term23 A y x)).
Proof. exact (TRANS (@lem3318116 A x' y x) (@lem3318121 A x' y x)). Qed.
Lemma lem3318123 {A : Type'} (x : A) (x' : A) (y : A) (h1 : x' = y) : (term23 A x' x) = (term23 A y x).
Proof. exact (EQ_MP (@lem3318122 A x' y x) (@lem3318113 A x x' y h1)). Qed.
Lemma lem3318124 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = y) : term23 A y x.
Proof. exact (EQ_MP (@lem3318123 A x x' y h2) (@lem3317958 A x s x' y h1)). Qed.
Lemma lem3318138 {A : Type'} (x : A) : (term99 A x) = (term99 A x).
Proof. exact (eq_refl (term99 A x)). Qed.
Lemma lem3318139 {A : Type'} (x : A) (x' : A) (y : A) (h1 : x' = y) : (term100 A x x') = (term100 A x y).
Proof. exact (MK_COMB (@lem3318138 A x) (@lem3317964 A x' y h1)). Qed.
Lemma lem3318140 {A : Type'} (y : A) (x : A) : (term100 A x y) = (y = x).
Proof. exact (eq_refl (term100 A x y)). Qed.
Lemma lem3318141 {A : Type'} (x : A) (x' : A) : (term101 A x x') = (term101 A x x').
Proof. exact (eq_refl (term101 A x x')). Qed.
Lemma lem3318142 {A : Type'} (x' : A) (y : A) (x : A) : ((term100 A x x') = (term100 A x y)) = ((term100 A x x') = (y = x)).
Proof. exact (MK_COMB (@lem3318141 A x x') (@lem3318140 A y x)). Qed.
Lemma lem3318143 {A : Type'} (x' : A) (x : A) : (term100 A x x') = (x' = x).
Proof. exact (eq_refl (term100 A x x')). Qed.
Lemma lem3318144 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3318145 {A : Type'} (x' : A) (x : A) : (term101 A x x') = (term102 A x' x).
Proof. exact (MK_COMB (@lem3318144) (@lem3318143 A x' x)). Qed.
Lemma lem3318146 {A : Type'} (y : A) (x : A) : (y = x) = (y = x).
Proof. exact (eq_refl (y = x)). Qed.
Lemma lem3318147 {A : Type'} (x' : A) (y : A) (x : A) : ((term100 A x x') = (y = x)) = ((x' = x) = (y = x)).
Proof. exact (MK_COMB (@lem3318145 A x' x) (@lem3318146 A y x)). Qed.
Lemma lem3318148 {A : Type'} (x' : A) (y : A) (x : A) : ((term100 A x x') = (term100 A x y)) = ((x' = x) = (y = x)).
Proof. exact (TRANS (@lem3318142 A x' y x) (@lem3318147 A x' y x)). Qed.
Lemma lem3318149 {A : Type'} (x : A) (x' : A) (y : A) (h1 : x' = y) : (x' = x) = (y = x).
Proof. exact (EQ_MP (@lem3318148 A x' y x) (@lem3318139 A x x' y h1)). Qed.
Lemma lem3318150 {A : Type'} (x : A) (x' : A) (y : A) (h1 : x' = x) (h2 : x' = y) : y = x.
Proof. exact (EQ_MP (@lem3318149 A x x' y h2) (@lem3317962 A x' x h1)). Qed.
Lemma lem3318178 {A : Type'} (x : A) : (term93 A x) = (term93 A x).
Proof. exact (eq_refl (term93 A x)). Qed.
Lemma lem3318179 {A : Type'} (x : A) (x' : A) (y : A) (h1 : x' = x) (h2 : x' = y) : (term94 A x y) = (term97 A x).
Proof. exact (MK_COMB (@lem3318178 A x) (@lem3318150 A x x' y h1 h2)). Qed.
Lemma lem3318180 {A : Type'} (x : A) : (term97 A x) = (term98 A x).
Proof. exact (eq_refl (term97 A x)). Qed.
Lemma lem3318181 {A : Type'} (x : A) (y : A) : (term95 A x y) = (term95 A x y).
Proof. exact (eq_refl (term95 A x y)). Qed.
Lemma lem3318182 {A : Type'} (y : A) (x : A) : ((term94 A x y) = (term97 A x)) = ((term94 A x y) = (term98 A x)).
Proof. exact (MK_COMB (@lem3318181 A x y) (@lem3318180 A x)). Qed.
Lemma lem3318183 {A : Type'} (y : A) (x : A) : (term94 A x y) = (term23 A y x).
Proof. exact (eq_refl (term94 A x y)). Qed.
Lemma lem3318184 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3318185 {A : Type'} (y : A) (x : A) : (term95 A x y) = (term96 A y x).
Proof. exact (MK_COMB (@lem3318184) (@lem3318183 A y x)). Qed.
Lemma lem3318186 {A : Type'} (x : A) : (term98 A x) = (term98 A x).
Proof. exact (eq_refl (term98 A x)). Qed.
Lemma lem3318187 {A : Type'} (y : A) (x : A) : ((term94 A x y) = (term98 A x)) = ((term23 A y x) = (term98 A x)).
Proof. exact (MK_COMB (@lem3318185 A y x) (@lem3318186 A x)). Qed.
Lemma lem3318188 {A : Type'} (y : A) (x : A) : ((term94 A x y) = (term97 A x)) = ((term23 A y x) = (term98 A x)).
Proof. exact (TRANS (@lem3318182 A y x) (@lem3318187 A y x)). Qed.
Lemma lem3318189 {A : Type'} (x : A) (x' : A) (y : A) (h1 : x' = x) (h2 : x' = y) : (term23 A y x) = (term98 A x).
Proof. exact (EQ_MP (@lem3318188 A y x) (@lem3318179 A x x' y h1 h2)). Qed.
Lemma lem3318190 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = x) (h3 : x' = y) : term98 A x.
Proof. exact (EQ_MP (@lem3318189 A x x' y h2 h3) (@lem3318124 A x s x' y h1 h3)). Qed.
Lemma lem3318245 {A : Type'} (y : A) : (term93 A y) = (term93 A y).
Proof. exact (eq_refl (term93 A y)). Qed.
Lemma lem3318246 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : (term94 A y x') = (term97 A y).
Proof. exact (MK_COMB (@lem3318245 A y) (@lem3317984 A x' y h1)). Qed.
Lemma lem3318247 {A : Type'} (y : A) : (term97 A y) = (term98 A y).
Proof. exact (eq_refl (term97 A y)). Qed.
Lemma lem3318248 {A : Type'} (y : A) (x' : A) : (term95 A y x') = (term95 A y x').
Proof. exact (eq_refl (term95 A y x')). Qed.
Lemma lem3318249 {A : Type'} (x' : A) (y : A) : ((term94 A y x') = (term97 A y)) = ((term94 A y x') = (term98 A y)).
Proof. exact (MK_COMB (@lem3318248 A y x') (@lem3318247 A y)). Qed.
Lemma lem3318250 {A : Type'} (x' : A) (y : A) : (term94 A y x') = (term23 A x' y).
Proof. exact (eq_refl (term94 A y x')). Qed.
Lemma lem3318251 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3318252 {A : Type'} (x' : A) (y : A) : (term95 A y x') = (term96 A x' y).
Proof. exact (MK_COMB (@lem3318251) (@lem3318250 A x' y)). Qed.
Lemma lem3318253 {A : Type'} (y : A) : (term98 A y) = (term98 A y).
Proof. exact (eq_refl (term98 A y)). Qed.
Lemma lem3318254 {A : Type'} (x' : A) (y : A) : ((term94 A y x') = (term98 A y)) = ((term23 A x' y) = (term98 A y)).
Proof. exact (MK_COMB (@lem3318252 A x' y) (@lem3318253 A y)). Qed.
Lemma lem3318255 {A : Type'} (x' : A) (y : A) : ((term94 A y x') = (term97 A y)) = ((term23 A x' y) = (term98 A y)).
Proof. exact (TRANS (@lem3318249 A x' y) (@lem3318254 A x' y)). Qed.
Lemma lem3318256 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : (term23 A x' y) = (term98 A y).
Proof. exact (EQ_MP (@lem3318255 A x' y) (@lem3318246 A x' y h1)). Qed.
Lemma lem3318257 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = y) : term98 A y.
Proof. exact (EQ_MP (@lem3318256 A x' y h2) (@lem3317980 A x s x' y h1)). Qed.
Lemma lem3318299 {A : Type'} (x : A) : (term93 A x) = (term93 A x).
Proof. exact (eq_refl (term93 A x)). Qed.
Lemma lem3318300 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term94 A x x') = (term97 A x).
Proof. exact (MK_COMB (@lem3318299 A x) (@lem3317988 A x' x h1)). Qed.
Lemma lem3318301 {A : Type'} (x : A) : (term97 A x) = (term98 A x).
Proof. exact (eq_refl (term97 A x)). Qed.
Lemma lem3318302 {A : Type'} (x : A) (x' : A) : (term95 A x x') = (term95 A x x').
Proof. exact (eq_refl (term95 A x x')). Qed.
Lemma lem3318303 {A : Type'} (x' : A) (x : A) : ((term94 A x x') = (term97 A x)) = ((term94 A x x') = (term98 A x)).
Proof. exact (MK_COMB (@lem3318302 A x x') (@lem3318301 A x)). Qed.
Lemma lem3318304 {A : Type'} (x' : A) (x : A) : (term94 A x x') = (term23 A x' x).
Proof. exact (eq_refl (term94 A x x')). Qed.
Lemma lem3318305 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3318306 {A : Type'} (x' : A) (x : A) : (term95 A x x') = (term96 A x' x).
Proof. exact (MK_COMB (@lem3318305) (@lem3318304 A x' x)). Qed.
Lemma lem3318307 {A : Type'} (x : A) : (term98 A x) = (term98 A x).
Proof. exact (eq_refl (term98 A x)). Qed.
Lemma lem3318308 {A : Type'} (x' : A) (x : A) : ((term94 A x x') = (term98 A x)) = ((term23 A x' x) = (term98 A x)).
Proof. exact (MK_COMB (@lem3318306 A x' x) (@lem3318307 A x)). Qed.
Lemma lem3318309 {A : Type'} (x' : A) (x : A) : ((term94 A x x') = (term97 A x)) = ((term23 A x' x) = (term98 A x)).
Proof. exact (TRANS (@lem3318303 A x' x) (@lem3318308 A x' x)). Qed.
Lemma lem3318310 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term23 A x' x) = (term98 A x).
Proof. exact (EQ_MP (@lem3318309 A x' x) (@lem3318300 A x' x h1)). Qed.
Lemma lem3318311 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term70 A x s x') (h2 : x' = x) : term98 A x.
Proof. exact (EQ_MP (@lem3318310 A x' x h2) (@lem3317990 A x s x' h1)). Qed.
Lemma lem3318352 {A : Type'} (x : A) (y : A) (h1 : term23 A x y) : term23 A x y.
Proof. exact (h1). Qed.
Lemma lem3318353 {A : Type'} (x : A) : (term99 A x) = (term99 A x).
Proof. exact (eq_refl (term99 A x)). Qed.
Lemma lem3318354 {A : Type'} (x : A) (x' : A) (y : A) (h1 : x' = y) : (term100 A x x') = (term100 A x y).
Proof. exact (MK_COMB (@lem3318353 A x) (@lem3317998 A x' y h1)). Qed.
Lemma lem3318355 {A : Type'} (y : A) (x : A) : (term100 A x y) = (y = x).
Proof. exact (eq_refl (term100 A x y)). Qed.
Lemma lem3318356 {A : Type'} (x : A) (x' : A) : (term101 A x x') = (term101 A x x').
Proof. exact (eq_refl (term101 A x x')). Qed.
Lemma lem3318357 {A : Type'} (x' : A) (y : A) (x : A) : ((term100 A x x') = (term100 A x y)) = ((term100 A x x') = (y = x)).
Proof. exact (MK_COMB (@lem3318356 A x x') (@lem3318355 A y x)). Qed.
Lemma lem3318358 {A : Type'} (x' : A) (x : A) : (term100 A x x') = (x' = x).
Proof. exact (eq_refl (term100 A x x')). Qed.
Lemma lem3318359 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3318360 {A : Type'} (x' : A) (x : A) : (term101 A x x') = (term102 A x' x).
Proof. exact (MK_COMB (@lem3318359) (@lem3318358 A x' x)). Qed.
Lemma lem3318361 {A : Type'} (y : A) (x : A) : (y = x) = (y = x).
Proof. exact (eq_refl (y = x)). Qed.
Lemma lem3318362 {A : Type'} (x' : A) (y : A) (x : A) : ((term100 A x x') = (y = x)) = ((x' = x) = (y = x)).
Proof. exact (MK_COMB (@lem3318360 A x' x) (@lem3318361 A y x)). Qed.
Lemma lem3318363 {A : Type'} (x' : A) (y : A) (x : A) : ((term100 A x x') = (term100 A x y)) = ((x' = x) = (y = x)).
Proof. exact (TRANS (@lem3318357 A x' y x) (@lem3318362 A x' y x)). Qed.
Lemma lem3318364 {A : Type'} (x : A) (x' : A) (y : A) (h1 : x' = y) : (x' = x) = (y = x).
Proof. exact (EQ_MP (@lem3318363 A x' y x) (@lem3318354 A x x' y h1)). Qed.
Lemma lem3318365 {A : Type'} (x : A) (x' : A) (y : A) (h1 : x' = x) (h2 : x' = y) : y = x.
Proof. exact (EQ_MP (@lem3318364 A x x' y h2) (@lem3317996 A x' x h1)). Qed.
Lemma lem3318380 {A : Type'} (x : A) : (term157 A x) = (term157 A x).
Proof. exact (eq_refl (term157 A x)). Qed.
Lemma lem3318381 {A : Type'} (x : A) (x' : A) (y : A) (h1 : x' = x) (h2 : x' = y) : (term158 A x y) = (term159 A x).
Proof. exact (MK_COMB (@lem3318380 A x) (@lem3318365 A x x' y h1 h2)). Qed.
Lemma lem3318382 {A : Type'} (x : A) : (term159 A x) = (term98 A x).
Proof. exact (eq_refl (term159 A x)). Qed.
Lemma lem3318383 {A : Type'} (x : A) (y : A) : (term160 A x y) = (term160 A x y).
Proof. exact (eq_refl (term160 A x y)). Qed.
Lemma lem3318384 {A : Type'} (y : A) (x : A) : ((term158 A x y) = (term159 A x)) = ((term158 A x y) = (term98 A x)).
Proof. exact (MK_COMB (@lem3318383 A x y) (@lem3318382 A x)). Qed.
Lemma lem3318385 {A : Type'} (x : A) (y : A) : (term158 A x y) = (term23 A x y).
Proof. exact (eq_refl (term158 A x y)). Qed.
Lemma lem3318386 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3318387 {A : Type'} (x : A) (y : A) : (term160 A x y) = (term96 A x y).
Proof. exact (MK_COMB (@lem3318386) (@lem3318385 A x y)). Qed.
Lemma lem3318388 {A : Type'} (x : A) : (term98 A x) = (term98 A x).
Proof. exact (eq_refl (term98 A x)). Qed.
Lemma lem3318389 {A : Type'} (y : A) (x : A) : ((term158 A x y) = (term98 A x)) = ((term23 A x y) = (term98 A x)).
Proof. exact (MK_COMB (@lem3318387 A x y) (@lem3318388 A x)). Qed.
Lemma lem3318390 {A : Type'} (y : A) (x : A) : ((term158 A x y) = (term159 A x)) = ((term23 A x y) = (term98 A x)).
Proof. exact (TRANS (@lem3318384 A y x) (@lem3318389 A y x)). Qed.
Lemma lem3318391 {A : Type'} (x : A) (x' : A) (y : A) (h1 : x' = x) (h2 : x' = y) : (term23 A x y) = (term98 A x).
Proof. exact (EQ_MP (@lem3318390 A y x) (@lem3318381 A x x' y h1 h2)). Qed.
Lemma lem3318392 {A : Type'} (x : A) (x' : A) (y : A) (h1 : term23 A x y) (h2 : x' = x) (h3 : x' = y) : term98 A x.
Proof. exact (EQ_MP (@lem3318391 A x x' y h2 h3) (@lem3318352 A x y h1)). Qed.
Lemma lem3318434 {A : Type'} (y : A) : (term93 A y) = (term93 A y).
Proof. exact (eq_refl (term93 A y)). Qed.
Lemma lem3318435 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : (term94 A y x') = (term97 A y).
Proof. exact (MK_COMB (@lem3318434 A y) (@lem3318016 A x' y h1)). Qed.
Lemma lem3318436 {A : Type'} (y : A) : (term97 A y) = (term98 A y).
Proof. exact (eq_refl (term97 A y)). Qed.
Lemma lem3318437 {A : Type'} (y : A) (x' : A) : (term95 A y x') = (term95 A y x').
Proof. exact (eq_refl (term95 A y x')). Qed.
Lemma lem3318438 {A : Type'} (x' : A) (y : A) : ((term94 A y x') = (term97 A y)) = ((term94 A y x') = (term98 A y)).
Proof. exact (MK_COMB (@lem3318437 A y x') (@lem3318436 A y)). Qed.
Lemma lem3318439 {A : Type'} (x' : A) (y : A) : (term94 A y x') = (term23 A x' y).
Proof. exact (eq_refl (term94 A y x')). Qed.
Lemma lem3318440 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3318441 {A : Type'} (x' : A) (y : A) : (term95 A y x') = (term96 A x' y).
Proof. exact (MK_COMB (@lem3318440) (@lem3318439 A x' y)). Qed.
Lemma lem3318442 {A : Type'} (y : A) : (term98 A y) = (term98 A y).
Proof. exact (eq_refl (term98 A y)). Qed.
Lemma lem3318443 {A : Type'} (x' : A) (y : A) : ((term94 A y x') = (term98 A y)) = ((term23 A x' y) = (term98 A y)).
Proof. exact (MK_COMB (@lem3318441 A x' y) (@lem3318442 A y)). Qed.
Lemma lem3318444 {A : Type'} (x' : A) (y : A) : ((term94 A y x') = (term97 A y)) = ((term23 A x' y) = (term98 A y)).
Proof. exact (TRANS (@lem3318438 A x' y) (@lem3318443 A x' y)). Qed.
Lemma lem3318445 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : (term23 A x' y) = (term98 A y).
Proof. exact (EQ_MP (@lem3318444 A x' y) (@lem3318435 A x' y h1)). Qed.
Lemma lem3318446 {A : Type'} (s : A -> Prop) (x' : A) (y : A) (h1 : term42 A s x' y) (h2 : x' = y) : term98 A y.
Proof. exact (EQ_MP (@lem3318445 A x' y h2) (@lem3318014 A s x' y h1)). Qed.
Lemma lem3318462 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3318463 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3318462 A x). Qed.
Lemma lem3318464 {A : Type'} (x : A) : term107 A x.
Proof. exact (fun h0 : term98 A x => @lem3318463 A x). Qed.
Lemma lem3318466 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3318467 {A : Type'} (x : A) : (term107 A x) = (x = x).
Proof. exact (@lem3318466 (x = x)). Qed.
Lemma lem3318468 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3318467 A x) (@lem3318464 A x)). Qed.
Lemma lem3318471 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3318473 {A : Type'} (x : A) : (term98 A x) = (term109 A x).
Proof. exact (@lem3318471 (x = x)). Qed.
Lemma lem3318476 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term152 A x s x' y) (h2 : x' = x) : term109 A x.
Proof. exact (EQ_MP (@lem3318473 A x) (@lem3318057 A s y x' x h1 h2)). Qed.
Lemma lem3318479 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term152 A x s x' y) (h2 : x' = x) : False.
Proof. exact (@lem3318476 A s y x' x h1 h2 (@lem3318468 A x)). Qed.
Lemma lem3318480 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term152 A x s x' y) (h2 : x' = x) : term110.
Proof. exact (fun h0 : ~ False => @lem3318479 A s y x' x h1 h2). Qed.
Lemma lem3318482 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3318483 : term110 = False.
Proof. exact (@lem3318482 False). Qed.
Lemma lem3318488 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3318489 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3318488 A x). Qed.
Lemma lem3318490 {A : Type'} (x : A) : term107 A x.
Proof. exact (fun h0 : term98 A x => @lem3318489 A x). Qed.
Lemma lem3318492 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3318493 {A : Type'} (x : A) : (term107 A x) = (x = x).
Proof. exact (@lem3318492 (x = x)). Qed.
Lemma lem3318494 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3318493 A x) (@lem3318490 A x)). Qed.
Lemma lem3318497 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3318499 {A : Type'} (x : A) : (term98 A x) = (term109 A x).
Proof. exact (@lem3318497 (x = x)). Qed.
Lemma lem3318502 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = x) (h3 : x' = y) : term109 A x.
Proof. exact (EQ_MP (@lem3318499 A x) (@lem3318190 A s x x' y h1 h2 h3)). Qed.
Lemma lem3318505 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = x) (h3 : x' = y) : False.
Proof. exact (@lem3318502 A s x x' y h1 h2 h3 (@lem3318494 A x)). Qed.
Lemma lem3318506 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = x) (h3 : x' = y) : term110.
Proof. exact (fun h0 : ~ False => @lem3318505 A s x x' y h1 h2 h3). Qed.
Lemma lem3318508 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3318509 : term110 = False.
Proof. exact (@lem3318508 False). Qed.
Lemma lem3318526 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3318527 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term111 A s x'.
Proof. exact (fun h0 : term92 A s x' => @lem3318526 A s x' h1). Qed.
Lemma lem3318529 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3318530 {A : Type'} (s : A -> Prop) (x' : A) : (term111 A s x') = (s x').
Proof. exact (@lem3318529 (s x')). Qed.
Lemma lem3318531 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3318530 A s x') (@lem3318527 A s x' h1)). Qed.
Lemma lem3318534 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3318536 {A : Type'} (s : A -> Prop) (x' : A) : (term92 A s x') = (term112 A s x').
Proof. exact (@lem3318534 (s x')). Qed.
Lemma lem3318539 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') : term112 A s x'.
Proof. exact (EQ_MP (@lem3318536 A s x') (@lem3317974 A s x' h1)). Qed.
Lemma lem3318542 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : False.
Proof. exact (@lem3318539 A s x' h1 (@lem3318531 A s x' h2)). Qed.
Lemma lem3318543 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : term110.
Proof. exact (fun h0 : ~ False => @lem3318542 A s x' h1 h2). Qed.
Lemma lem3318545 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3318546 : term110 = False.
Proof. exact (@lem3318545 False). Qed.
Lemma lem3318547 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3318546) (@lem3318543 A s x' h1 h2)). Qed.
Lemma lem3318563 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3318564 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3318563 A x). Qed.
Lemma lem3318565 {A : Type'} (y : A) : y = y.
Proof. exact (@lem3318564 A y). Qed.
Lemma lem3318566 {A : Type'} (y : A) : term107 A y.
Proof. exact (fun h0 : term98 A y => @lem3318565 A y). Qed.
Lemma lem3318568 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3318569 {A : Type'} (y : A) : (term107 A y) = (y = y).
Proof. exact (@lem3318568 (y = y)). Qed.
Lemma lem3318570 {A : Type'} (y : A) : y = y.
Proof. exact (EQ_MP (@lem3318569 A y) (@lem3318566 A y)). Qed.
Lemma lem3318573 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3318575 {A : Type'} (y : A) : (term98 A y) = (term109 A y).
Proof. exact (@lem3318573 (y = y)). Qed.
Lemma lem3318578 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = y) : term109 A y.
Proof. exact (EQ_MP (@lem3318575 A y) (@lem3318257 A x s x' y h1 h2)). Qed.
Lemma lem3318581 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = y) : False.
Proof. exact (@lem3318578 A x s x' y h1 h2 (@lem3318570 A y)). Qed.
Lemma lem3318582 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = y) : term110.
Proof. exact (fun h0 : ~ False => @lem3318581 A x s x' y h1 h2). Qed.
Lemma lem3318584 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3318585 : term110 = False.
Proof. exact (@lem3318584 False). Qed.
Lemma lem3318602 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3318603 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3318602 A x). Qed.
Lemma lem3318604 {A : Type'} (x : A) : term107 A x.
Proof. exact (fun h0 : term98 A x => @lem3318603 A x). Qed.
Lemma lem3318606 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3318607 {A : Type'} (x : A) : (term107 A x) = (x = x).
Proof. exact (@lem3318606 (x = x)). Qed.
Lemma lem3318608 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3318607 A x) (@lem3318604 A x)). Qed.
Lemma lem3318611 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3318613 {A : Type'} (x : A) : (term98 A x) = (term109 A x).
Proof. exact (@lem3318611 (x = x)). Qed.
Lemma lem3318616 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term70 A x s x') (h2 : x' = x) : term109 A x.
Proof. exact (EQ_MP (@lem3318613 A x) (@lem3318311 A s x' x h1 h2)). Qed.
Lemma lem3318619 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term70 A x s x') (h2 : x' = x) : False.
Proof. exact (@lem3318616 A s x' x h1 h2 (@lem3318608 A x)). Qed.
Lemma lem3318620 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term70 A x s x') (h2 : x' = x) : term110.
Proof. exact (fun h0 : ~ False => @lem3318619 A s x' x h1 h2). Qed.
Lemma lem3318622 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3318623 : term110 = False.
Proof. exact (@lem3318622 False). Qed.
Lemma lem3318628 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3318629 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3318628 A x). Qed.
Lemma lem3318630 {A : Type'} (x : A) : term107 A x.
Proof. exact (fun h0 : term98 A x => @lem3318629 A x). Qed.
Lemma lem3318632 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3318633 {A : Type'} (x : A) : (term107 A x) = (x = x).
Proof. exact (@lem3318632 (x = x)). Qed.
Lemma lem3318634 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3318633 A x) (@lem3318630 A x)). Qed.
Lemma lem3318637 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3318639 {A : Type'} (x : A) : (term98 A x) = (term109 A x).
Proof. exact (@lem3318637 (x = x)). Qed.
Lemma lem3318642 {A : Type'} (x : A) (x' : A) (y : A) (h1 : term23 A x y) (h2 : x' = x) (h3 : x' = y) : term109 A x.
Proof. exact (EQ_MP (@lem3318639 A x) (@lem3318392 A x x' y h1 h2 h3)). Qed.
Lemma lem3318645 {A : Type'} (x : A) (x' : A) (y : A) (h1 : term23 A x y) (h2 : x' = x) (h3 : x' = y) : False.
Proof. exact (@lem3318642 A x x' y h1 h2 h3 (@lem3318634 A x)). Qed.
Lemma lem3318646 {A : Type'} (x : A) (x' : A) (y : A) (h1 : term23 A x y) (h2 : x' = x) (h3 : x' = y) : term110.
Proof. exact (fun h0 : ~ False => @lem3318645 A x x' y h1 h2 h3). Qed.
Lemma lem3318648 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3318649 : term110 = False.
Proof. exact (@lem3318648 False). Qed.
Lemma lem3318666 {A : Type'} (s : A -> Prop) (x' : A) (y : A) (h1 : term42 A s x' y) : s x'.
Proof. exact (proj1 (@lem3317790 A s x' y h1)). Qed.
Lemma lem3318667 {A : Type'} (s : A -> Prop) (x' : A) (y : A) (h1 : term42 A s x' y) : term111 A s x'.
Proof. exact (fun h0 : term92 A s x' => @lem3318666 A s x' y h1). Qed.
Lemma lem3318669 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3318670 {A : Type'} (s : A -> Prop) (x' : A) : (term111 A s x') = (s x').
Proof. exact (@lem3318669 (s x')). Qed.
Lemma lem3318671 {A : Type'} (s : A -> Prop) (x' : A) (y : A) (h1 : term42 A s x' y) : s x'.
Proof. exact (EQ_MP (@lem3318670 A s x') (@lem3318667 A s x' y h1)). Qed.
Lemma lem3318674 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3318676 {A : Type'} (s : A -> Prop) (x' : A) : (term92 A s x') = (term112 A s x').
Proof. exact (@lem3318674 (s x')). Qed.
Lemma lem3318679 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term70 A x s x') : term112 A s x'.
Proof. exact (EQ_MP (@lem3318676 A s x') (@lem3318008 A x s x' h1)). Qed.
Lemma lem3318682 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term70 A x s x') (h2 : term42 A s x' y) : False.
Proof. exact (@lem3318679 A x s x' h1 (@lem3318671 A s x' y h2)). Qed.
Lemma lem3318683 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term70 A x s x') (h2 : term42 A s x' y) : term110.
Proof. exact (fun h0 : ~ False => @lem3318682 A x s x' y h1 h2). Qed.
Lemma lem3318685 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3318686 : term110 = False.
Proof. exact (@lem3318685 False). Qed.
Lemma lem3318687 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term70 A x s x') (h2 : term42 A s x' y) : False.
Proof. exact (EQ_MP (@lem3318686) (@lem3318683 A x s x' y h1 h2)). Qed.
Lemma lem3318703 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3318704 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3318703 A x). Qed.
Lemma lem3318705 {A : Type'} (y : A) : y = y.
Proof. exact (@lem3318704 A y). Qed.
Lemma lem3318706 {A : Type'} (y : A) : term107 A y.
Proof. exact (fun h0 : term98 A y => @lem3318705 A y). Qed.
Lemma lem3318708 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3318709 {A : Type'} (y : A) : (term107 A y) = (y = y).
Proof. exact (@lem3318708 (y = y)). Qed.
Lemma lem3318710 {A : Type'} (y : A) : y = y.
Proof. exact (EQ_MP (@lem3318709 A y) (@lem3318706 A y)). Qed.
Lemma lem3318713 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3318715 {A : Type'} (y : A) : (term98 A y) = (term109 A y).
Proof. exact (@lem3318713 (y = y)). Qed.
Lemma lem3318718 {A : Type'} (s : A -> Prop) (x' : A) (y : A) (h1 : term42 A s x' y) (h2 : x' = y) : term109 A y.
Proof. exact (EQ_MP (@lem3318715 A y) (@lem3318446 A s x' y h1 h2)). Qed.
Lemma lem3318721 {A : Type'} (s : A -> Prop) (x' : A) (y : A) (h1 : term42 A s x' y) (h2 : x' = y) : False.
Proof. exact (@lem3318718 A s x' y h1 h2 (@lem3318710 A y)). Qed.
Lemma lem3318722 {A : Type'} (s : A -> Prop) (x' : A) (y : A) (h1 : term42 A s x' y) (h2 : x' = y) : term110.
Proof. exact (fun h0 : ~ False => @lem3318721 A s x' y h1 h2). Qed.
Lemma lem3318724 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3318725 : term110 = False.
Proof. exact (@lem3318724 False). Qed.
Lemma lem3318727 {A : Type'} (s : A -> Prop) (x' : A) (y : A) (h1 : term42 A s x' y) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3318725) (@lem3318722 A s x' y h1 h2)). Qed.
Lemma lem3318728 {A : Type'} (x : A) (x' : A) (y : A) (h1 : term23 A x y) (h2 : x' = x) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem3318649) (@lem3318646 A x x' y h1 h2 h3)). Qed.
Lemma lem3318729 {A : Type'} (x : A) (x' : A) (y : A) (h1 : term23 A x y) (h2 : x' = x) (h3 : x' = y) : (term23 A x y) = False.
Proof. exact (prop_ext (fun h4 : term23 A x y => @lem3318728 A x x' y h1 h2 h3) (fun h4 : False => @lem3318352 A x y h1)). Qed.
Lemma lem3318731 {A : Type'} (x : A) (x' : A) (y : A) (h1 : term23 A x y) (h2 : x' = x) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem3318729 A x x' y h1 h2 h3) (@lem3318352 A x y h1)). Qed.
Lemma lem3318732 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term70 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3318623) (@lem3318620 A s x' x h1 h2)). Qed.
Lemma lem3318733 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3318585) (@lem3318582 A x s x' y h1 h2)). Qed.
Lemma lem3318735 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = x) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem3318509) (@lem3318506 A s x x' y h1 h2 h3)). Qed.
Lemma lem3318736 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term152 A x s x' y) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3318483) (@lem3318480 A s y x' x h1 h2)). Qed.
Lemma lem3318737 {A : Type'} (s : A -> Prop) (x' : A) (y : A) (h1 : term42 A s x' y) (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3318727 A s x' y h1 h2) (fun h3 : False => @lem3318016 A x' y h2)). Qed.
Lemma lem3318738 {A : Type'} (s : A -> Prop) (x' : A) (y : A) (h1 : term42 A s x' y) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3318737 A s x' y h1 h2) (@lem3318016 A x' y h2)). Qed.
Lemma lem3318739 {A : Type'} (x : A) (x' : A) (y : A) (h1 : term23 A x y) (h2 : x' = x) (h3 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h4 : x' = y => @lem3318731 A x x' y h1 h2 h3) (fun h4 : False => @lem3317998 A x' y h3)). Qed.
Lemma lem3318740 {A : Type'} (x : A) (x' : A) (y : A) (h1 : term23 A x y) (h2 : x' = x) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem3318739 A x x' y h1 h2 h3) (@lem3317998 A x' y h3)). Qed.
Lemma lem3318741 {A : Type'} (x : A) (x' : A) (y : A) (h1 : term23 A x y) (h2 : x' = x) (h3 : x' = y) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3318740 A x x' y h1 h2 h3) (fun h4 : False => @lem3317996 A x' x h2)). Qed.
Lemma lem3318742 {A : Type'} (x : A) (x' : A) (y : A) (h1 : term23 A x y) (h2 : x' = x) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem3318741 A x x' y h1 h2 h3) (@lem3317996 A x' x h2)). Qed.
Lemma lem3318743 {A : Type'} (x : A) (x' : A) (y : A) (h1 : term23 A x y) (h2 : x' = x) (h3 : x' = y) : (term23 A x y) = False.
Proof. exact (prop_ext (fun h4 : term23 A x y => @lem3318742 A x x' y h1 h2 h3) (fun h4 : False => @lem3317994 A x y h1)). Qed.
Lemma lem3318744 {A : Type'} (x : A) (x' : A) (y : A) (h1 : term23 A x y) (h2 : x' = x) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem3318743 A x x' y h1 h2 h3) (@lem3317994 A x y h1)). Qed.
Lemma lem3318745 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term70 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3318732 A s x' x h1 h2) (fun h3 : False => @lem3317988 A x' x h2)). Qed.
Lemma lem3318746 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term70 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3318745 A s x' x h1 h2) (@lem3317988 A x' x h2)). Qed.
Lemma lem3318747 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3318733 A x s x' y h1 h2) (fun h3 : False => @lem3317984 A x' y h2)). Qed.
Lemma lem3318748 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3318747 A x s x' y h1 h2) (@lem3317984 A x' y h2)). Qed.
Lemma lem3318749 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : (term92 A s x') = False.
Proof. exact (prop_ext (fun h3 : term92 A s x' => @lem3318547 A s x' h1 h2) (fun h3 : False => @lem3317974 A s x' h1)). Qed.
Lemma lem3318750 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3318749 A s x' h1 h2) (@lem3317974 A s x' h1)). Qed.
Lemma lem3318751 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3318750 A s x' h1 h2) (fun h3 : False => @lem3317972 A s x' h2)). Qed.
Lemma lem3318752 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3318751 A s x' h1 h2) (@lem3317972 A s x' h2)). Qed.
Lemma lem3318753 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = x) (h3 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h4 : x' = y => @lem3318735 A s x x' y h1 h2 h3) (fun h4 : False => @lem3317964 A x' y h3)). Qed.
Lemma lem3318754 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = x) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem3318753 A s x x' y h1 h2 h3) (@lem3317964 A x' y h3)). Qed.
Lemma lem3318755 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = x) (h3 : x' = y) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3318754 A s x x' y h1 h2 h3) (fun h4 : False => @lem3317962 A x' x h2)). Qed.
Lemma lem3318756 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = x) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem3318755 A s x x' y h1 h2 h3) (@lem3317962 A x' x h2)). Qed.
Lemma lem3318757 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term152 A x s x' y) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3318736 A s y x' x h1 h2) (fun h3 : False => @lem3317952 A x' x h2)). Qed.
Lemma lem3318758 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term152 A x s x' y) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3318757 A s y x' x h1 h2) (@lem3317952 A x' x h2)). Qed.
Lemma lem3318759 {A : Type'} (s : A -> Prop) (x' : A) (y : A) (h1 : term42 A s x' y) (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3318738 A s x' y h1 h2) (fun h3 : False => @lem3317944 A x' y h2)). Qed.
Lemma lem3318760 {A : Type'} (s : A -> Prop) (x' : A) (y : A) (h1 : term42 A s x' y) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3318759 A s x' y h1 h2) (@lem3317944 A x' y h2)). Qed.
Lemma lem3318761 {A : Type'} (x : A) (x' : A) (y : A) (h1 : term23 A x y) (h2 : x' = x) (h3 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h4 : x' = y => @lem3318744 A x x' y h1 h2 h3) (fun h4 : False => @lem3317908 A x' y h3)). Qed.
Lemma lem3318762 {A : Type'} (x : A) (x' : A) (y : A) (h1 : term23 A x y) (h2 : x' = x) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem3318761 A x x' y h1 h2 h3) (@lem3317908 A x' y h3)). Qed.
Lemma lem3318763 {A : Type'} (x : A) (x' : A) (y : A) (h1 : term23 A x y) (h2 : x' = x) (h3 : x' = y) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3318762 A x x' y h1 h2 h3) (fun h4 : False => @lem3317904 A x' x h2)). Qed.
Lemma lem3318764 {A : Type'} (x : A) (x' : A) (y : A) (h1 : term23 A x y) (h2 : x' = x) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem3318763 A x x' y h1 h2 h3) (@lem3317904 A x' x h2)). Qed.
Lemma lem3318765 {A : Type'} (x : A) (x' : A) (y : A) (h1 : term23 A x y) (h2 : x' = x) (h3 : x' = y) : (term23 A x y) = False.
Proof. exact (prop_ext (fun h4 : term23 A x y => @lem3318764 A x x' y h1 h2 h3) (fun h4 : False => @lem3317900 A x y h1)). Qed.
Lemma lem3318766 {A : Type'} (x : A) (x' : A) (y : A) (h1 : term23 A x y) (h2 : x' = x) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem3318765 A x x' y h1 h2 h3) (@lem3317900 A x y h1)). Qed.
Lemma lem3318767 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term70 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3318746 A s x' x h1 h2) (fun h3 : False => @lem3317888 A x' x h2)). Qed.
Lemma lem3318768 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term70 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3318767 A s x' x h1 h2) (@lem3317888 A x' x h2)). Qed.
Lemma lem3318769 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3318748 A x s x' y h1 h2) (fun h3 : False => @lem3317880 A x' y h2)). Qed.
Lemma lem3318770 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3318769 A x s x' y h1 h2) (@lem3317880 A x' y h2)). Qed.
Lemma lem3318771 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : (term92 A s x') = False.
Proof. exact (prop_ext (fun h3 : term92 A s x' => @lem3318752 A s x' h1 h2) (fun h3 : False => @lem3317860 A s x' h1)). Qed.
Lemma lem3318772 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3318771 A s x' h1 h2) (@lem3317860 A s x' h1)). Qed.
Lemma lem3318773 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3318772 A s x' h1 h2) (fun h3 : False => @lem3317856 A s x' h2)). Qed.
Lemma lem3318774 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3318773 A s x' h1 h2) (@lem3317856 A s x' h2)). Qed.
Lemma lem3318775 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = x) (h3 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h4 : x' = y => @lem3318756 A s x x' y h1 h2 h3) (fun h4 : False => @lem3317840 A x' y h3)). Qed.
Lemma lem3318776 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = x) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem3318775 A s x x' y h1 h2 h3) (@lem3317840 A x' y h3)). Qed.
Lemma lem3318777 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = x) (h3 : x' = y) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3318776 A s x x' y h1 h2 h3) (fun h4 : False => @lem3317836 A x' x h2)). Qed.
Lemma lem3318778 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = x) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem3318777 A s x x' y h1 h2 h3) (@lem3317836 A x' x h2)). Qed.
Lemma lem3318779 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term152 A x s x' y) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3318758 A s y x' x h1 h2) (fun h3 : False => @lem3317816 A x' x h2)). Qed.
Lemma lem3318780 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term152 A x s x' y) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3318779 A s y x' x h1 h2) (@lem3317816 A x' x h2)). Qed.
Lemma lem3318781 {A : Type'} (s : A -> Prop) (x' : A) (y : A) (h1 : term42 A s x' y) (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3318760 A s x' y h1 h2) (fun h3 : False => @lem3317944 A x' y h2)). Qed.
Lemma lem3318782 {A : Type'} (s : A -> Prop) (x' : A) (y : A) (h1 : term42 A s x' y) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3318781 A s x' y h1 h2) (@lem3317944 A x' y h2)). Qed.
Lemma lem3318783 {A : Type'} (x : A) (x' : A) (y : A) (h1 : term23 A x y) (h2 : x' = x) (h3 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h4 : x' = y => @lem3318766 A x x' y h1 h2 h3) (fun h4 : False => @lem3317908 A x' y h3)). Qed.
Lemma lem3318784 {A : Type'} (x : A) (x' : A) (y : A) (h1 : term23 A x y) (h2 : x' = x) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem3318783 A x x' y h1 h2 h3) (@lem3317908 A x' y h3)). Qed.
Lemma lem3318785 {A : Type'} (x : A) (x' : A) (y : A) (h1 : term23 A x y) (h2 : x' = x) (h3 : x' = y) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3318784 A x x' y h1 h2 h3) (fun h4 : False => @lem3317904 A x' x h2)). Qed.
Lemma lem3318786 {A : Type'} (x : A) (x' : A) (y : A) (h1 : term23 A x y) (h2 : x' = x) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem3318785 A x x' y h1 h2 h3) (@lem3317904 A x' x h2)). Qed.
Lemma lem3318787 {A : Type'} (x : A) (x' : A) (y : A) (h1 : term23 A x y) (h2 : x' = x) (h3 : x' = y) : (term23 A x y) = False.
Proof. exact (prop_ext (fun h4 : term23 A x y => @lem3318786 A x x' y h1 h2 h3) (fun h4 : False => @lem3317900 A x y h1)). Qed.
Lemma lem3318788 {A : Type'} (x : A) (x' : A) (y : A) (h1 : term23 A x y) (h2 : x' = x) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem3318787 A x x' y h1 h2 h3) (@lem3317900 A x y h1)). Qed.
Lemma lem3318789 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term70 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3318768 A s x' x h1 h2) (fun h3 : False => @lem3317888 A x' x h2)). Qed.
Lemma lem3318790 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term70 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3318789 A s x' x h1 h2) (@lem3317888 A x' x h2)). Qed.
Lemma lem3318791 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3318770 A x s x' y h1 h2) (fun h3 : False => @lem3317880 A x' y h2)). Qed.
Lemma lem3318792 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3318791 A x s x' y h1 h2) (@lem3317880 A x' y h2)). Qed.
Lemma lem3318793 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : (term92 A s x') = False.
Proof. exact (prop_ext (fun h3 : term92 A s x' => @lem3318774 A s x' h1 h2) (fun h3 : False => @lem3317860 A s x' h1)). Qed.
Lemma lem3318794 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3318793 A s x' h1 h2) (@lem3317860 A s x' h1)). Qed.
Lemma lem3318795 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3318794 A s x' h1 h2) (fun h3 : False => @lem3317856 A s x' h2)). Qed.
Lemma lem3318796 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term92 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3318795 A s x' h1 h2) (@lem3317856 A s x' h2)). Qed.
Lemma lem3318797 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = x) (h3 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h4 : x' = y => @lem3318778 A s x x' y h1 h2 h3) (fun h4 : False => @lem3317840 A x' y h3)). Qed.
Lemma lem3318798 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = x) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem3318797 A s x x' y h1 h2 h3) (@lem3317840 A x' y h3)). Qed.
Lemma lem3318799 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = x) (h3 : x' = y) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3318798 A s x x' y h1 h2 h3) (fun h4 : False => @lem3317836 A x' x h2)). Qed.
Lemma lem3318800 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term152 A x s x' y) (h2 : x' = x) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem3318799 A s x x' y h1 h2 h3) (@lem3317836 A x' x h2)). Qed.
Lemma lem3318801 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term152 A x s x' y) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3318780 A s y x' x h1 h2) (fun h3 : False => @lem3317816 A x' x h2)). Qed.
Lemma lem3318802 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term152 A x s x' y) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3318801 A s y x' x h1 h2) (@lem3317816 A x' x h2)). Qed.
Lemma lem3318803 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term42 A s x' y) (h2 : term150 A x s x' y) : False.
Proof. exact (or_elim (@lem3317788 A x s x' y h2) (fun h0 : term70 A x s x' => @lem3318687 A x s x' y h0 h1) (fun h0 : x' = y => @lem3318782 A s x' y h1 h0)). Qed.
Lemma lem3318804 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term23 A x y) (h2 : term150 A x s x' y) (h3 : x' = x) : False.
Proof. exact (or_elim (@lem3317788 A x s x' y h2) (fun h0 : term70 A x s x' => @lem3318790 A s x' x h0 h3) (fun h0 : x' = y => @lem3318788 A x x' y h1 h3 h0)). Qed.
Lemma lem3318805 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term23 A x y) (h2 : term150 A x s x' y) : False.
Proof. exact (or_elim (@lem3317787 A x s x' y h2) (fun h0 : x' = x => @lem3318804 A s y x' x h1 h2 h0) (fun h0 : term42 A s x' y => @lem3318803 A x s x' y h0 h2)). Qed.
Lemma lem3318806 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : s x') (h2 : term152 A x s x' y) : False.
Proof. exact (or_elim (@lem3317777 A x s x' y h2) (fun h0 : term92 A s x' => @lem3318796 A s x' h0 h1) (fun h0 : x' = y => @lem3318792 A x s x' y h2 h0)). Qed.
Lemma lem3318807 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term152 A x s x' y) (h2 : x' = x) : False.
Proof. exact (or_elim (@lem3317777 A x s x' y h1) (fun h0 : term92 A s x' => @lem3318802 A s y x' x h1 h2) (fun h0 : x' = y => @lem3318800 A s x x' y h1 h2 h0)). Qed.
Lemma lem3318808 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term152 A x s x' y) : False.
Proof. exact (or_elim (@lem3317780 A x s x' y h1) (fun h0 : x' = x => @lem3318807 A s y x' x h1 h0) (fun h0 : s x' => @lem3318806 A x s x' y h0 h1)). Qed.
Lemma lem3318809 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term23 A x y) (h2 : term144 A x s x' y) : False.
Proof. exact (or_elim (@lem3317772 A x s x' y h2) (fun h0 : term152 A x s x' y => @lem3318808 A x s x' y h0) (fun h0 : term150 A x s x' y => @lem3318805 A x s x' y h1 h0)). Qed.
Lemma lem3318810 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term23 A x y) (h2 : term144 A x s x' y) : (term23 A x y) = False.
Proof. exact (prop_ext (fun h3 : term23 A x y => @lem3318809 A x s x' y h1 h2) (fun h3 : False => @lem3317674 A x y h1)). Qed.
Lemma lem3318811 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term23 A x y) (h2 : term144 A x s x' y) : False.
Proof. exact (EQ_MP (@lem3318810 A x s x' y h1 h2) (@lem3317674 A x y h1)). Qed.
Lemma lem3318812 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term23 A x y) (h2 : term144 A x s x' y) : (term23 A x y) = False.
Proof. exact (prop_ext (fun h3 : term23 A x y => @lem3318811 A x s x' y h1 h2) (fun h3 : False => @lem3317602 A x y h1)). Qed.
Lemma lem3318813 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term23 A x y) (h2 : term144 A x s x' y) : False.
Proof. exact (EQ_MP (@lem3318812 A x s x' y h1 h2) (@lem3317602 A x y h1)). Qed.
Lemma lem3318814 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term23 A x y) (h2 : term144 A x s x' y) : (term144 A x s x' y) = False.
Proof. exact (prop_ext (fun h3 : term144 A x s x' y => @lem3318813 A x s x' y h1 h2) (fun h3 : False => @lem3317596 A x s x' y h2)). Qed.
Lemma lem3318815 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term23 A x y) (h2 : term144 A x s x' y) : False.
Proof. exact (EQ_MP (@lem3318814 A x s x' y h1 h2) (@lem3317596 A x s x' y h2)). Qed.
Lemma lem3318816 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (y : A) (h1 : term23 A x y) : term143 A x s x' y.
Proof. exact (fun h0 : term144 A x s x' y => @lem3318815 A x s x' y h1 h0). Qed.
Lemma lem3318817 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (y : A) (h1 : term23 A x y) : (term37 A x s x' y) = (term120 A x s x' y).
Proof. exact (EQ_MP (@lem3317595 A x s x' y) (@lem3318816 A s x' x y h1)). Qed.
Lemma lem3318822 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term23 A x y) : term123 A x s y.
Proof. exact (fun x' : A => @lem3318817 A s x' x y h1). Qed.
Lemma lem3318823 {A : Type'} (x : A) (s : A -> Prop) (y : A) : term124 A x s y.
Proof. exact (fun h0 : term23 A x y => @lem3318822 A s x y h0). Qed.
Lemma lem3318828 {A : Type'} (s : A -> Prop) (y : A) : term134 A s y.
Proof. exact (fun x : A => @lem3318823 A x s y). Qed.
Lemma lem3318833 {A : Type'} (y : A) : term138 A y.
Proof. exact (fun s : A -> Prop => @lem3318828 A s y). Qed.
Lemma lem3318838 {A : Type'} : term142 A.
Proof. exact (fun y : A => @lem3318833 A y). Qed.
Lemma lem3318839 {A : Type'} : term141 A.
Proof. exact (EQ_MP (@lem3317590 A) (@lem3318838 A)). Qed.
Lemma lem3318840 {A : Type'} (y : A) : term161 A y.
Proof. exact (@lem3318839 A y). Qed.
Lemma lem3318841 {A : Type'} (y : A) : (term161 A y) = (term137 A y).
Proof. exact (eq_refl (term161 A y)). Qed.
Lemma lem3318842 {A : Type'} (y : A) : term137 A y.
Proof. exact (EQ_MP (@lem3318841 A y) (@lem3318840 A y)). Qed.
Lemma lem3318843 {A : Type'} (y : A) (s : A -> Prop) : term162 A y s.
Proof. exact (@lem3318842 A y s). Qed.
Lemma lem3318844 {A : Type'} (s : A -> Prop) (y : A) : (term162 A y s) = (term133 A s y).
Proof. exact (eq_refl (term162 A y s)). Qed.
Lemma lem3318845 {A : Type'} (s : A -> Prop) (y : A) : term133 A s y.
Proof. exact (EQ_MP (@lem3318844 A s y) (@lem3318843 A y s)). Qed.
Lemma lem3318846 {A : Type'} (s : A -> Prop) (y : A) (x : A) : term163 A s y x.
Proof. exact (@lem3318845 A s y x). Qed.
Lemma lem3318847 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term163 A s y x) = (term125 A x s y).
Proof. exact (eq_refl (term163 A s y x)). Qed.
Lemma lem3318848 {A : Type'} (x : A) (s : A -> Prop) (y : A) : term125 A x s y.
Proof. exact (EQ_MP (@lem3318847 A x s y) (@lem3318846 A s y x)). Qed.
Lemma lem3318850 {A : Type'} (x : A) (s : A -> Prop) (y : A) : term125 A x s y.
Proof. exact (@lem3317451 A x s y (@lem3318848 A x s y)). Qed.
Lemma lem3318851 {A : Type'} (x : A) (s : A -> Prop) (y : A) (h1 : term126 A x s y) : False.
Proof. exact (@lem3318850 A x s y (@lem3317435 A x s y h1)). Qed.
Lemma lem3318852 {A : Type'} (x : A) (s : A -> Prop) (y : A) (h1 : term126 A x s y) : (term126 A x s y) = False.
Proof. exact (prop_ext (fun h2 : term126 A x s y => @lem3318851 A x s y h1) (fun h2 : False => @lem3317435 A x s y h1)). Qed.
Lemma lem3318853 {A : Type'} (x : A) (s : A -> Prop) (y : A) (h1 : term126 A x s y) : False.
Proof. exact (EQ_MP (@lem3318852 A x s y h1) (@lem3317435 A x s y h1)). Qed.
Lemma lem3318854 {A : Type'} (x : A) (s : A -> Prop) (y : A) : term125 A x s y.
Proof. exact (fun h0 : term126 A x s y => @lem3318853 A x s y h0). Qed.
Lemma lem3318855 {A : Type'} (x : A) (s : A -> Prop) (y : A) : term124 A x s y.
Proof. exact (EQ_MP (@lem3317434 A x s y) (@lem3318854 A x s y)). Qed.
Lemma lem3318856 {A : Type'} (x : A) (s : A -> Prop) (y : A) : term117 A x s y.
Proof. exact (EQ_MP (@lem3317430 A x s y) (@lem3318855 A x s y)). Qed.
Lemma lem3318857 {A : Type'} (x : A) (s : A -> Prop) (y : A) : term12 A x s y.
Proof. exact (EQ_MP (@lem3317339 A x s y) (@lem3318856 A x s y)). Qed.
Lemma lem3318860 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term23 A x y) : (term9 A x s y) = (term7 A x s y).
Proof. exact (@lem3318857 A x s y (@lem3315876 A x y h1)). Qed.
Lemma lem3318861 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term23 A x y) : (term23 A x y) = ((term9 A x s y) = (term7 A x s y)).
Proof. exact (prop_ext (fun h2 : term23 A x y => @lem3318860 A s x y h1) (fun h2 : (term9 A x s y) = (term7 A x s y) => @lem3315876 A x y h1)). Qed.
Lemma lem3318862 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term23 A x y) : (term9 A x s y) = (term7 A x s y).
Proof. exact (EQ_MP (@lem3318861 A s x y h1) (@lem3315876 A x y h1)). Qed.
Lemma lem3318863 {A : Type'} (x : A) (s : A -> Prop) (y : A) : term12 A x s y.
Proof. exact (fun h0 : term23 A x y => @lem3318862 A s x y h0). Qed.
Lemma lem3318864 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : x = y) : (term9 A x s y) = (@DELETE A s y).
Proof. exact (@lem3317314 A x s y (@lem3315859 A x y h1)). Qed.
Lemma lem3318865 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : x = y) : (x = y) = ((term9 A x s y) = (@DELETE A s y)).
Proof. exact (prop_ext (fun h2 : x = y => @lem3318864 A s x y h1) (fun h2 : (term9 A x s y) = (@DELETE A s y) => @lem3315859 A x y h1)). Qed.
Lemma lem3318866 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : x = y) : (term9 A x s y) = (@DELETE A s y).
Proof. exact (EQ_MP (@lem3318865 A s x y h1) (@lem3315859 A x y h1)). Qed.
Lemma lem3318867 {A : Type'} (x : A) (s : A -> Prop) (y : A) : term16 A x s y.
Proof. exact (fun h0 : x = y => @lem3318866 A s x y h0). Qed.
Lemma lem3318868 {A : Type'} (x : A) (s : A -> Prop) (y : A) : term19 A x s y.
Proof. exact (conj (@lem3318867 A x s y) (@lem3318863 A x s y)). Qed.
Lemma lem3318869 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term9 A x s y) = (term20 A x s y).
Proof. exact (EQ_MP (@lem3315858 A x s y) (@lem3318868 A x s y)). Qed.
Lemma lem3318874 {A : Type'} (x : A) (y : A) : term164 A x y.
Proof. exact (fun s : A -> Prop => @lem3318869 A x s y). Qed.
Lemma lem3318879 {A : Type'} (x : A) : term165 A x.
Proof. exact (fun y : A => @lem3318874 A x y). Qed.
Lemma lem3318884 {A : Type'} : term166 A.
Proof. exact (fun x : A => @lem3318879 A x). Qed.
