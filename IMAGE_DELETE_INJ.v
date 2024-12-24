Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_DELETE_INJ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3379795 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3379796 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3379797 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3379796 t1) (@lem3379795 t1)). Qed.
Lemma lem3379798 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3379797 t1 t2). Qed.
Lemma lem3379799 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3379800 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3379799 t1 t2) (@lem3379798 t1 t2)). Qed.
Lemma lem3379801 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3379800 t1 t2 t3). Qed.
Lemma lem3379802 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3379803 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3379802 t1 t2 t3) (@lem3379801 t1 t2 t3)). Qed.
Lemma lem3379804 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3379803 t1 t2 t3)). Qed.
Lemma lem3379838 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term7 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3379839 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term7 B s t).
Proof. exact (@lem3379838 B s t). Qed.
Lemma lem3379840 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : ((term8 A B f s a) = (term9 A B s f a)) = (term10 A B s f a).
Proof. exact (@lem3379839 B (term8 A B f s a) (term9 A B s f a)). Qed.
Lemma lem3379849 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term11 A B s f a) = (term11 A B s f a).
Proof. exact (eq_refl (term11 A B s f a)). Qed.
Lemma lem3379850 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term12 A B s f a) = (term13 A B s f a).
Proof. exact (MK_COMB (@lem3379849 A B s f a) (@lem3379840 A B s f a)). Qed.
Lemma lem3379853 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term14 A B s f) = (term15 A B s f).
Proof. exact (fun_ext (fun a : A => @lem3379850 A B s f a)). Qed.
Lemma lem3379854 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3379855 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term16 A B s f) = (term17 A B s f).
Proof. exact (MK_COMB (@lem3379854 A) (@lem3379853 A B s f)). Qed.
Lemma lem3379860 {A B : Type'} (f : A -> B) : (term18 A B f) = (term19 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3379855 A B s f)). Qed.
Lemma lem3379861 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3379862 {A B : Type'} (f : A -> B) : (term20 A B f) = (term21 A B f).
Proof. exact (MK_COMB (@lem3379861 A) (@lem3379860 A B f)). Qed.
Lemma lem3379867 {A B : Type'} : (term22 A B) = (term23 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3379862 A B f)). Qed.
Lemma lem3379868 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3379869 {A B : Type'} : (term24 A B) = (term25 A B).
Proof. exact (MK_COMB (@lem3379868 A B) (@lem3379867 A B)). Qed.
Lemma lem3379874 {A B : Type'} : (term25 A B) = (term24 A B).
Proof. exact (SYM (@lem3379869 A B)). Qed.
Lemma lem3379898 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3379899 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3379898 A P x). Qed.
Lemma lem3379900 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3379899 A s x). Qed.
Lemma lem3379901 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3379902 {A : Type'} (s : A -> Prop) (x : A) : (term26 A x s) = (term27 A s x).
Proof. exact (MK_COMB (@lem3379901) (@lem3379900 A s x)). Qed.
Lemma lem3379905 {A B : Type'} (x : A) (f : A -> B) (a : A) : ((f x) = (f a)) = ((f x) = (f a)).
Proof. exact (eq_refl ((f x) = (f a))). Qed.
Lemma lem3379906 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (a : A) : (term28 A B s x f a) = (term29 A B s x f a).
Proof. exact (MK_COMB (@lem3379902 A s x) (@lem3379905 A B x f a)). Qed.
Lemma lem3379909 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3379910 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (a : A) : (term30 A B s x f a) = (term31 A B s x f a).
Proof. exact (MK_COMB (@lem3379909) (@lem3379906 A B s x f a)). Qed.
Lemma lem3379913 {A : Type'} (x : A) (a : A) : (x = a) = (x = a).
Proof. exact (eq_refl (x = a)). Qed.
Lemma lem3379914 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (a : A) : (term32 A B s f x a) = (term33 A B s f x a).
Proof. exact (MK_COMB (@lem3379910 A B s x f a) (@lem3379913 A x a)). Qed.
Lemma lem3379917 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term34 A B s f a) = (term35 A B s f a).
Proof. exact (fun_ext (fun x : A => @lem3379914 A B s f x a)). Qed.
Lemma lem3379918 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3379919 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term36 A B s f a) = (term37 A B s f a).
Proof. exact (MK_COMB (@lem3379918 A) (@lem3379917 A B s f a)). Qed.
Lemma lem3379924 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3379925 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term11 A B s f a) = (term38 A B s f a).
Proof. exact (MK_COMB (@lem3379924) (@lem3379919 A B s f a)). Qed.
Lemma lem3379933 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term39 A B y f s) = (term40 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3379934 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term39 A B y f s) = (term40 A B y f s).
Proof. exact (@lem3379933 A B y f s). Qed.
Lemma lem3379935 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term41 A B x f s a) = (term42 A B x f s a).
Proof. exact (@lem3379934 A B x f (@DELETE A s a)). Qed.
Lemma lem3379945 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term43 A x s y) = (term44 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3379946 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term43 A x s y) = (term44 A s x y).
Proof. exact (@lem3379945 A s x y). Qed.
Lemma lem3379947 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term43 A x s a) = (term44 A s x a).
Proof. exact (@lem3379946 A s x a). Qed.
Lemma lem3379951 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3379952 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3379951 A P x). Qed.
Lemma lem3379953 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3379952 A s x). Qed.
Lemma lem3379954 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3379955 {A : Type'} (s : A -> Prop) (x : A) : (term26 A x s) = (term27 A s x).
Proof. exact (MK_COMB (@lem3379954) (@lem3379953 A s x)). Qed.
Lemma lem3379958 {A : Type'} (x : A) (a : A) : (term45 A x a) = (term45 A x a).
Proof. exact (eq_refl (term45 A x a)). Qed.
Lemma lem3379959 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term44 A s x a) = (term46 A s x a).
Proof. exact (MK_COMB (@lem3379955 A s x) (@lem3379958 A x a)). Qed.
Lemma lem3379962 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term43 A x s a) = (term46 A s x a).
Proof. exact (TRANS (@lem3379947 A s x a) (@lem3379959 A s x a)). Qed.
Lemma lem3379963 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term47 A B x f x') = (term47 A B x f x').
Proof. exact (eq_refl (term47 A B x f x')). Qed.
Lemma lem3379964 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term48 A B x f x' s a) = (term49 A B x f s x' a).
Proof. exact (MK_COMB (@lem3379963 A B x f x') (@lem3379962 A s x' a)). Qed.
Lemma lem3379967 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term50 A B x f s a) = (term51 A B x f s a).
Proof. exact (fun_ext (fun x' : A => @lem3379964 A B x f s x' a)). Qed.
Lemma lem3379968 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3379969 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term42 A B x f s a) = (term52 A B x f s a).
Proof. exact (MK_COMB (@lem3379968 A) (@lem3379967 A B x f s a)). Qed.
Lemma lem3379974 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term41 A B x f s a) = (term52 A B x f s a).
Proof. exact (TRANS (@lem3379935 A B x f s a) (@lem3379969 A B x f s a)). Qed.
Lemma lem3379975 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3379976 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term53 A B x f s a) = (term54 A B x f s a).
Proof. exact (MK_COMB (@lem3379975) (@lem3379974 A B x f s a)). Qed.
Lemma lem3379978 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term43 A x s y) = (term44 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3379979 {B : Type'} (s : B -> Prop) (x : B) (y : B) : (term43 B x s y) = (term44 B s x y).
Proof. exact (@lem3379978 B s x y). Qed.
Lemma lem3379980 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term55 A B x s f a) = (term56 A B s x f a).
Proof. exact (@lem3379979 B (@IMAGE A B f s) x (f a)). Qed.
Lemma lem3379984 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term39 A B y f s) = (term40 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3379985 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term39 A B y f s) = (term40 A B y f s).
Proof. exact (@lem3379984 A B y f s). Qed.
Lemma lem3379986 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term39 A B x f s) = (term40 A B x f s).
Proof. exact (@lem3379985 A B x f s). Qed.
Lemma lem3379996 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3379997 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3379996 A P x). Qed.
Lemma lem3379998 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3379997 A s x). Qed.
Lemma lem3379999 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term47 A B x f x') = (term47 A B x f x').
Proof. exact (eq_refl (term47 A B x f x')). Qed.
Lemma lem3380000 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term57 A B x f x' s) = (term58 A B x f s x').
Proof. exact (MK_COMB (@lem3379999 A B x f x') (@lem3379998 A s x')). Qed.
Lemma lem3380003 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term59 A B x f s) = (term60 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3380000 A B x f s x')). Qed.
Lemma lem3380004 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3380005 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term40 A B x f s) = (term61 A B x f s).
Proof. exact (MK_COMB (@lem3380004 A) (@lem3380003 A B x f s)). Qed.
Lemma lem3380010 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term39 A B x f s) = (term61 A B x f s).
Proof. exact (TRANS (@lem3379986 A B x f s) (@lem3380005 A B x f s)). Qed.
Lemma lem3380011 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3380012 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term62 A B x f s) = (term63 A B x f s).
Proof. exact (MK_COMB (@lem3380011) (@lem3380010 A B x f s)). Qed.
Lemma lem3380015 {A B : Type'} (x : B) (f : A -> B) (a : A) : (term64 A B x f a) = (term64 A B x f a).
Proof. exact (eq_refl (term64 A B x f a)). Qed.
Lemma lem3380016 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term56 A B s x f a) = (term65 A B s x f a).
Proof. exact (MK_COMB (@lem3380012 A B x f s) (@lem3380015 A B x f a)). Qed.
Lemma lem3380019 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term55 A B x s f a) = (term65 A B s x f a).
Proof. exact (TRANS (@lem3379980 A B s x f a) (@lem3380016 A B s x f a)). Qed.
Lemma lem3380020 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : ((term41 A B x f s a) = (term55 A B x s f a)) = ((term52 A B x f s a) = (term65 A B s x f a)).
Proof. exact (MK_COMB (@lem3379976 A B x f s a) (@lem3380019 A B s x f a)). Qed.
Lemma lem3380023 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term66 A B s f a) = (term67 A B s f a).
Proof. exact (fun_ext (fun x : B => @lem3380020 A B s x f a)). Qed.
Lemma lem3380024 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3380025 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term10 A B s f a) = (term68 A B s f a).
Proof. exact (MK_COMB (@lem3380024 B) (@lem3380023 A B s f a)). Qed.
Lemma lem3380030 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term13 A B s f a) = (term69 A B s f a).
Proof. exact (MK_COMB (@lem3379925 A B s f a) (@lem3380025 A B s f a)). Qed.
Lemma lem3380033 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term15 A B s f) = (term70 A B s f).
Proof. exact (fun_ext (fun a : A => @lem3380030 A B s f a)). Qed.
Lemma lem3380034 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3380035 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term17 A B s f) = (term71 A B s f).
Proof. exact (MK_COMB (@lem3380034 A) (@lem3380033 A B s f)). Qed.
Lemma lem3380040 {A B : Type'} (f : A -> B) : (term19 A B f) = (term72 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3380035 A B s f)). Qed.
Lemma lem3380041 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3380042 {A B : Type'} (f : A -> B) : (term21 A B f) = (term73 A B f).
Proof. exact (MK_COMB (@lem3380041 A) (@lem3380040 A B f)). Qed.
Lemma lem3380047 {A B : Type'} : (term23 A B) = (term74 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3380042 A B f)). Qed.
Lemma lem3380048 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3380049 {A B : Type'} : (term25 A B) = (term75 A B).
Proof. exact (MK_COMB (@lem3380048 A B) (@lem3380047 A B)). Qed.
Lemma lem3380054 {A B : Type'} : (term75 A B) = (term25 A B).
Proof. exact (SYM (@lem3380049 A B)). Qed.
Lemma lem3380056 (p : Prop) : p = (term76 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3380057 {A B : Type'} : (term75 A B) = (term77 A B).
Proof. exact (@lem3380056 (term75 A B)). Qed.
Lemma lem3380058 {A B : Type'} : (term77 A B) = (term75 A B).
Proof. exact (SYM (@lem3380057 A B)). Qed.
Lemma lem3380059 {A B : Type'} (h1 : term78 A B) : term78 A B.
Proof. exact (h1). Qed.
Lemma lem3380062 {A B : Type'} (h1 : term77 A B) : term77 A B.
Proof. exact (h1). Qed.
Lemma lem3380063 {A B : Type'} : term79 A B.
Proof. exact (fun h0 : term77 A B => @lem3380062 A B h0). Qed.
Lemma lem3380064 {A B : Type'} (h1 : term79 A B) : term79 A B.
Proof. exact (h1). Qed.
Lemma lem3380065 {A B : Type'} (h1 : term77 A B) : term77 A B.
Proof. exact (h1). Qed.
Lemma lem3380066 {A B : Type'} (h1 : term77 A B) (h2 : term79 A B) : term77 A B.
Proof. exact (@lem3380064 A B h2 (@lem3380065 A B h1)). Qed.
Lemma lem3380067 {A B : Type'} (h1 : term77 A B) : term80 A B.
Proof. exact (fun h0 : term79 A B => @lem3380066 A B h1 h0). Qed.
Lemma lem3380068 {A B : Type'} (h1 : term79 A B) : term79 A B.
Proof. exact (h1). Qed.
Lemma lem3380069 {A B : Type'} (h1 : term77 A B) (h2 : term79 A B) : term77 A B.
Proof. exact (@lem3380067 A B h1 (@lem3380068 A B h2)). Qed.
Lemma lem3380070 {A B : Type'} (h1 : term79 A B) : term79 A B.
Proof. exact (fun h0 : term77 A B => @lem3380069 A B h0 h1). Qed.
Lemma lem3380071 {A B : Type'} : term81 A B.
Proof. exact (fun h0 : term79 A B => @lem3380070 A B h0). Qed.
Lemma lem3380074 {A B : Type'} : term79 A B.
Proof. exact (@lem3380071 A B (@lem3380063 A B)). Qed.
Lemma lem3380075 {A B : Type'} : term79 A B.
Proof. exact (@lem3380074 A B). Qed.
Lemma lem3380077 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3380078 {A B : Type'} : (term77 A B) = (term82 A B).
Proof. exact (@lem3380077 (term78 A B)). Qed.
Lemma lem3380080 (t : Prop) : (term83 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3380081 {A B : Type'} : (term82 A B) = (term75 A B).
Proof. exact (@lem3380080 (term75 A B)). Qed.
Lemma lem3380200 {A B : Type'} : (term77 A B) = (term75 A B).
Proof. exact (TRANS (@lem3380078 A B) (@lem3380081 A B)). Qed.
Lemma lem3380203 {A B : Type'} (x : B) (f : A -> B) (a : A) : (term64 A B x f a) = (term64 A B x f a).
Proof. exact (eq_refl (term64 A B x f a)). Qed.
Lemma lem3380208 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term58 A B x f s x') = (term58 A B x f s x').
Proof. exact (eq_refl (term58 A B x f s x')). Qed.
Lemma lem3380209 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term60 A B x f s) = (term60 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3380208 A B x f s x')). Qed.
Lemma lem3380210 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3380211 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term61 A B x f s) = (term61 A B x f s).
Proof. exact (MK_COMB (@lem3380210 A) (@lem3380209 A B x f s)). Qed.
Lemma lem3380212 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3380213 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term63 A B x f s) = (term63 A B x f s).
Proof. exact (MK_COMB (@lem3380212) (@lem3380211 A B x f s)). Qed.
Lemma lem3380214 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term65 A B s x f a) = (term65 A B s x f a).
Proof. exact (MK_COMB (@lem3380213 A B x f s) (@lem3380203 A B x f a)). Qed.
Lemma lem3380225 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term49 A B x f s x' a) = (term49 A B x f s x' a).
Proof. exact (eq_refl (term49 A B x f s x' a)). Qed.
Lemma lem3380226 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term51 A B x f s a) = (term51 A B x f s a).
Proof. exact (fun_ext (fun x' : A => @lem3380225 A B x f s x' a)). Qed.
Lemma lem3380227 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3380228 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term52 A B x f s a) = (term52 A B x f s a).
Proof. exact (MK_COMB (@lem3380227 A) (@lem3380226 A B x f s a)). Qed.
Lemma lem3380229 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3380230 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term54 A B x f s a) = (term54 A B x f s a).
Proof. exact (MK_COMB (@lem3380229) (@lem3380228 A B x f s a)). Qed.
Lemma lem3380231 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : ((term52 A B x f s a) = (term65 A B s x f a)) = ((term52 A B x f s a) = (term65 A B s x f a)).
Proof. exact (MK_COMB (@lem3380230 A B x f s a) (@lem3380214 A B s x f a)). Qed.
Lemma lem3380232 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term67 A B s f a) = (term67 A B s f a).
Proof. exact (fun_ext (fun x : B => @lem3380231 A B s x f a)). Qed.
Lemma lem3380233 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3380234 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term68 A B s f a) = (term68 A B s f a).
Proof. exact (MK_COMB (@lem3380233 B) (@lem3380232 A B s f a)). Qed.
Lemma lem3380243 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (a : A) : (term33 A B s f x a) = (term33 A B s f x a).
Proof. exact (eq_refl (term33 A B s f x a)). Qed.
Lemma lem3380244 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term35 A B s f a) = (term35 A B s f a).
Proof. exact (fun_ext (fun x : A => @lem3380243 A B s f x a)). Qed.
Lemma lem3380245 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3380246 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term37 A B s f a) = (term37 A B s f a).
Proof. exact (MK_COMB (@lem3380245 A) (@lem3380244 A B s f a)). Qed.
Lemma lem3380247 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3380248 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term38 A B s f a) = (term38 A B s f a).
Proof. exact (MK_COMB (@lem3380247) (@lem3380246 A B s f a)). Qed.
Lemma lem3380249 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term69 A B s f a) = (term69 A B s f a).
Proof. exact (MK_COMB (@lem3380248 A B s f a) (@lem3380234 A B s f a)). Qed.
Lemma lem3380250 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term70 A B s f) = (term70 A B s f).
Proof. exact (fun_ext (fun a : A => @lem3380249 A B s f a)). Qed.
Lemma lem3380251 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3380252 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term71 A B s f) = (term71 A B s f).
Proof. exact (MK_COMB (@lem3380251 A) (@lem3380250 A B s f)). Qed.
Lemma lem3380253 {A B : Type'} (f : A -> B) : (term72 A B f) = (term72 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3380252 A B s f)). Qed.
Lemma lem3380254 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3380255 {A B : Type'} (f : A -> B) : (term73 A B f) = (term73 A B f).
Proof. exact (MK_COMB (@lem3380254 A) (@lem3380253 A B f)). Qed.
Lemma lem3380256 {A B : Type'} : (term74 A B) = (term74 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3380255 A B f)). Qed.
Lemma lem3380257 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3380258 {A B : Type'} : (term75 A B) = (term75 A B).
Proof. exact (MK_COMB (@lem3380257 A B) (@lem3380256 A B)). Qed.
Lemma lem3380317 {A B : Type'} : (term77 A B) = (term75 A B).
Proof. exact (TRANS (@lem3380200 A B) (@lem3380258 A B)). Qed.
Lemma lem3380318 {A B : Type'} : (term75 A B) = (term77 A B).
Proof. exact (SYM (@lem3380317 A B)). Qed.
Lemma lem3380319 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) (h1 : term37 A B s f a) : term37 A B s f a.
Proof. exact (h1). Qed.
Lemma lem3380321 (p : Prop) : p = (term76 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3380322 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : ((term52 A B x f s a) = (term65 A B s x f a)) = (term84 A B s x f a).
Proof. exact (@lem3380321 ((term52 A B x f s a) = (term65 A B s x f a))). Qed.
Lemma lem3380323 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term84 A B s x f a) = ((term52 A B x f s a) = (term65 A B s x f a)).
Proof. exact (SYM (@lem3380322 A B s x f a)). Qed.
Lemma lem3380324 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term85 A B s x f a) : term85 A B s x f a.
Proof. exact (h1). Qed.
Lemma lem3380331 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (a : A) : (term86 A B s x f a) = (term87 A B s x f a).
Proof. exact (@lem17045 (s x) ((f x) = (f a))). Qed.
Lemma lem3380332 {A : Type'} (x : A) (a : A) : (x = a) = (x = a).
Proof. exact (eq_refl (x = a)). Qed.
Lemma lem3380333 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3380334 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (a : A) : (term88 A B s x f a) = (term89 A B s x f a).
Proof. exact (MK_COMB (@lem3380333) (@lem3380331 A B s x f a)). Qed.
Lemma lem3380335 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (a : A) : (term90 A B s f x a) = (term91 A B s f x a).
Proof. exact (MK_COMB (@lem3380334 A B s x f a) (@lem3380332 A x a)). Qed.
Lemma lem3380336 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (a : A) : (term33 A B s f x a) = (term90 A B s f x a).
Proof. exact (@lem17265 (term29 A B s x f a) (x = a)). Qed.
Lemma lem3380337 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (a : A) : (term33 A B s f x a) = (term91 A B s f x a).
Proof. exact (TRANS (@lem3380336 A B s f x a) (@lem3380335 A B s f x a)). Qed.
Lemma lem3380338 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term35 A B s f a) = (term92 A B s f a).
Proof. exact (fun_ext (fun x : A => @lem3380337 A B s f x a)). Qed.
Lemma lem3380339 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3380392 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term37 A B s f a) = (term93 A B s f a).
Proof. exact (MK_COMB (@lem3380339 A) (@lem3380338 A B s f a)). Qed.
Lemma lem3380393 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) (h1 : term37 A B s f a) : term93 A B s f a.
Proof. exact (EQ_MP (@lem3380392 A B s f a) (@lem3380319 A B s f a h1)). Qed.
Lemma lem3380401 {A : Type'} (x : A) (a : A) : (term94 A x a) = (x = a).
Proof. exact (@lem16933 (x = a)). Qed.
Lemma lem3380403 {A : Type'} (s : A -> Prop) (x : A) : (term95 A s x) = (term95 A s x).
Proof. exact (eq_refl (term95 A s x)). Qed.
Lemma lem3380404 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term96 A s x a) = (term97 A s x a).
Proof. exact (MK_COMB (@lem3380403 A s x) (@lem3380401 A x a)). Qed.
Lemma lem3380405 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term98 A s x a) = (term96 A s x a).
Proof. exact (@lem17045 (s x) (term45 A x a)). Qed.
Lemma lem3380406 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term98 A s x a) = (term97 A s x a).
Proof. exact (TRANS (@lem3380405 A s x a) (@lem3380404 A s x a)). Qed.
Lemma lem3380411 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term99 A B x f x') = (term99 A B x f x').
Proof. exact (eq_refl (term99 A B x f x')). Qed.
Lemma lem3380412 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term100 A B x f s x' a) = (term101 A B x f s x' a).
Proof. exact (MK_COMB (@lem3380411 A B x f x') (@lem3380406 A s x' a)). Qed.
Lemma lem3380413 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term102 A B x f s x' a) = (term100 A B x f s x' a).
Proof. exact (@lem17045 (x = (f x')) (term46 A s x' a)). Qed.
Lemma lem3380414 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term102 A B x f s x' a) = (term101 A B x f s x' a).
Proof. exact (TRANS (@lem3380413 A B x f s x' a) (@lem3380412 A B x f s x' a)). Qed.
Lemma lem3380417 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term49 A B x f s x' a) = (term49 A B x f s x' a).
Proof. exact (eq_refl (term49 A B x f s x' a)). Qed.
Lemma lem3380418 {A : Type'} (P : A -> Prop) : (term103 A P) = (term104 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3380419 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term105 A B x f s a) = (term106 A B x f s a).
Proof. exact (@lem3380418 A (term51 A B x f s a)). Qed.
Lemma lem3380420 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term107 A B x f s a x') = (term49 A B x f s x' a).
Proof. exact (eq_refl (term107 A B x f s a x')). Qed.
Lemma lem3380421 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3380422 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term108 A B x f s a x') = (term102 A B x f s x' a).
Proof. exact (MK_COMB (@lem3380421) (@lem3380420 A B x f s x' a)). Qed.
Lemma lem3380423 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term108 A B x f s a x') = (term101 A B x f s x' a).
Proof. exact (TRANS (@lem3380422 A B x f s x' a) (@lem3380414 A B x f s x' a)). Qed.
Lemma lem3380424 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term109 A B x f s a) = (term110 A B x f s a).
Proof. exact (fun_ext (fun x' : A => @lem3380423 A B x f s x' a)). Qed.
Lemma lem3380425 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3380426 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term106 A B x f s a) = (term111 A B x f s a).
Proof. exact (MK_COMB (@lem3380425 A) (@lem3380424 A B x f s a)). Qed.
Lemma lem3380427 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term105 A B x f s a) = (term111 A B x f s a).
Proof. exact (TRANS (@lem3380419 A B x f s a) (@lem3380426 A B x f s a)). Qed.
Lemma lem3380428 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term51 A B x f s a) = (term51 A B x f s a).
Proof. exact (fun_ext (fun x' : A => @lem3380417 A B x f s x' a)). Qed.
Lemma lem3380429 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3380430 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term52 A B x f s a) = (term52 A B x f s a).
Proof. exact (MK_COMB (@lem3380429 A) (@lem3380428 A B x f s a)). Qed.
Lemma lem3380439 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term112 A B x f s x') = (term113 A B x f s x').
Proof. exact (@lem17045 (x = (f x')) (s x')). Qed.
Lemma lem3380442 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term58 A B x f s x') = (term58 A B x f s x').
Proof. exact (eq_refl (term58 A B x f s x')). Qed.
Lemma lem3380443 {A : Type'} (P : A -> Prop) : (term103 A P) = (term104 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3380444 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term114 A B x f s) = (term115 A B x f s).
Proof. exact (@lem3380443 A (term60 A B x f s)). Qed.
Lemma lem3380445 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term116 A B x f s x') = (term58 A B x f s x').
Proof. exact (eq_refl (term116 A B x f s x')). Qed.
Lemma lem3380446 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3380447 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term117 A B x f s x') = (term112 A B x f s x').
Proof. exact (MK_COMB (@lem3380446) (@lem3380445 A B x f s x')). Qed.
Lemma lem3380448 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term117 A B x f s x') = (term113 A B x f s x').
Proof. exact (TRANS (@lem3380447 A B x f s x') (@lem3380439 A B x f s x')). Qed.
Lemma lem3380449 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term118 A B x f s) = (term119 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3380448 A B x f s x')). Qed.
Lemma lem3380450 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3380451 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term115 A B x f s) = (term120 A B x f s).
Proof. exact (MK_COMB (@lem3380450 A) (@lem3380449 A B x f s)). Qed.
Lemma lem3380452 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term114 A B x f s) = (term120 A B x f s).
Proof. exact (TRANS (@lem3380444 A B x f s) (@lem3380451 A B x f s)). Qed.
Lemma lem3380453 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term60 A B x f s) = (term60 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3380442 A B x f s x')). Qed.
Lemma lem3380454 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3380455 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term61 A B x f s) = (term61 A B x f s).
Proof. exact (MK_COMB (@lem3380454 A) (@lem3380453 A B x f s)). Qed.
Lemma lem3380456 {A B : Type'} (x : B) (f : A -> B) (a : A) : (term64 A B x f a) = (term64 A B x f a).
Proof. exact (eq_refl (term64 A B x f a)). Qed.
Lemma lem3380459 {A B : Type'} (x : B) (f : A -> B) (a : A) : (term121 A B x f a) = (x = (f a)).
Proof. exact (@lem16933 (x = (f a))). Qed.
Lemma lem3380460 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3380461 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term122 A B x f s) = (term123 A B x f s).
Proof. exact (MK_COMB (@lem3380460) (@lem3380452 A B x f s)). Qed.
Lemma lem3380462 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term124 A B s x f a) = (term125 A B s x f a).
Proof. exact (MK_COMB (@lem3380461 A B x f s) (@lem3380459 A B x f a)). Qed.
Lemma lem3380463 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term126 A B s x f a) = (term124 A B s x f a).
Proof. exact (@lem17045 (term61 A B x f s) (term64 A B x f a)). Qed.
Lemma lem3380464 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term126 A B s x f a) = (term125 A B s x f a).
Proof. exact (TRANS (@lem3380463 A B s x f a) (@lem3380462 A B s x f a)). Qed.
Lemma lem3380465 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3380466 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term63 A B x f s) = (term63 A B x f s).
Proof. exact (MK_COMB (@lem3380465) (@lem3380455 A B x f s)). Qed.
Lemma lem3380467 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term65 A B s x f a) = (term65 A B s x f a).
Proof. exact (MK_COMB (@lem3380466 A B x f s) (@lem3380456 A B x f a)). Qed.
Lemma lem3380468 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3380469 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term127 A B x f s a) = (term128 A B x f s a).
Proof. exact (MK_COMB (@lem3380468) (@lem3380427 A B x f s a)). Qed.
Lemma lem3380470 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term129 A B s x f a) = (term130 A B s x f a).
Proof. exact (MK_COMB (@lem3380469 A B x f s a) (@lem3380467 A B s x f a)). Qed.
Lemma lem3380471 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3380472 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term131 A B x f s a) = (term131 A B x f s a).
Proof. exact (MK_COMB (@lem3380471) (@lem3380430 A B x f s a)). Qed.
Lemma lem3380473 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term132 A B s x f a) = (term133 A B s x f a).
Proof. exact (MK_COMB (@lem3380472 A B x f s a) (@lem3380464 A B s x f a)). Qed.
Lemma lem3380474 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3380475 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term134 A B s x f a) = (term135 A B s x f a).
Proof. exact (MK_COMB (@lem3380474) (@lem3380473 A B s x f a)). Qed.
Lemma lem3380476 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term136 A B s x f a) = (term137 A B s x f a).
Proof. exact (MK_COMB (@lem3380475 A B s x f a) (@lem3380470 A B s x f a)). Qed.
Lemma lem3380477 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term85 A B s x f a) = (term136 A B s x f a).
Proof. exact (@lem17646 (term52 A B x f s a) (term65 A B s x f a)). Qed.
Lemma lem3380478 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term85 A B s x f a) = (term137 A B s x f a).
Proof. exact (TRANS (@lem3380477 A B s x f a) (@lem3380476 A B s x f a)). Qed.
Lemma lem3380657 {A : Type'} (P : A -> Prop) (Q : Prop) : (term138 A P Q) = (term139 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3380658 {A : Type'} (P : A -> Prop) (Q : Prop) : (term138 A P Q) = (term139 A P Q).
Proof. exact (@lem3380657 A P Q). Qed.
Lemma lem3380659 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term140 A B s x f a) = (term141 A B s x f a).
Proof. exact (@lem3380658 A (term51 A B x f s a) (term125 A B s x f a)). Qed.
Lemma lem3380660 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term107 A B x f s a x') = (term49 A B x f s x' a).
Proof. exact (eq_refl (term107 A B x f s a x')). Qed.
Lemma lem3380661 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term142 A B x f s a) = (term51 A B x f s a).
Proof. exact (fun_ext (fun x' : A => @lem3380660 A B x f s x' a)). Qed.
Lemma lem3380662 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3380663 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term143 A B x f s a) = (term52 A B x f s a).
Proof. exact (MK_COMB (@lem3380662 A) (@lem3380661 A B x f s a)). Qed.
Lemma lem3380664 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3380665 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term144 A B x f s a) = (term131 A B x f s a).
Proof. exact (MK_COMB (@lem3380664) (@lem3380663 A B x f s a)). Qed.
Lemma lem3380666 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term125 A B s x f a) = (term125 A B s x f a).
Proof. exact (eq_refl (term125 A B s x f a)). Qed.
Lemma lem3380667 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term140 A B s x f a) = (term133 A B s x f a).
Proof. exact (MK_COMB (@lem3380665 A B x f s a) (@lem3380666 A B s x f a)). Qed.
Lemma lem3380668 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3380669 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term145 A B s x f a) = (term146 A B s x f a).
Proof. exact (MK_COMB (@lem3380668) (@lem3380667 A B s x f a)). Qed.
Lemma lem3380670 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term107 A B x f s a x') = (term49 A B x f s x' a).
Proof. exact (eq_refl (term107 A B x f s a x')). Qed.
Lemma lem3380671 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3380672 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term147 A B x f s a x') = (term148 A B x f s x' a).
Proof. exact (MK_COMB (@lem3380671) (@lem3380670 A B x f s x' a)). Qed.
Lemma lem3380673 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term125 A B s x f a) = (term125 A B s x f a).
Proof. exact (eq_refl (term125 A B s x f a)). Qed.
Lemma lem3380674 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (a : A) : (term149 A B x s x' f a) = (term150 A B x s x' f a).
Proof. exact (MK_COMB (@lem3380672 A B x' f s x a) (@lem3380673 A B s x' f a)). Qed.
Lemma lem3380675 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term151 A B s x f a) = (term152 A B s x f a).
Proof. exact (fun_ext (fun x' : A => @lem3380674 A B x' s x f a)). Qed.
Lemma lem3380676 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3380677 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term141 A B s x f a) = (term153 A B s x f a).
Proof. exact (MK_COMB (@lem3380676 A) (@lem3380675 A B s x f a)). Qed.
Lemma lem3380678 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : ((term140 A B s x f a) = (term141 A B s x f a)) = ((term133 A B s x f a) = (term153 A B s x f a)).
Proof. exact (MK_COMB (@lem3380669 A B s x f a) (@lem3380677 A B s x f a)). Qed.
Lemma lem3380679 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term133 A B s x f a) = (term153 A B s x f a).
Proof. exact (EQ_MP (@lem3380678 A B s x f a) (@lem3380659 A B s x f a)). Qed.
Lemma lem3380680 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3380681 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term135 A B s x f a) = (term154 A B s x f a).
Proof. exact (MK_COMB (@lem3380680) (@lem3380679 A B s x f a)). Qed.
Lemma lem3380683 {A : Type'} (P : A -> Prop) (Q : Prop) : (term138 A P Q) = (term139 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3380684 {A : Type'} (P : A -> Prop) (Q : Prop) : (term138 A P Q) = (term139 A P Q).
Proof. exact (@lem3380683 A P Q). Qed.
Lemma lem3380685 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term155 A B s x f a) = (term156 A B s x f a).
Proof. exact (@lem3380684 A (term60 A B x f s) (term64 A B x f a)). Qed.
Lemma lem3380686 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term116 A B x f s x') = (term58 A B x f s x').
Proof. exact (eq_refl (term116 A B x f s x')). Qed.
Lemma lem3380687 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term157 A B x f s) = (term60 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3380686 A B x f s x')). Qed.
Lemma lem3380688 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3380689 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term158 A B x f s) = (term61 A B x f s).
Proof. exact (MK_COMB (@lem3380688 A) (@lem3380687 A B x f s)). Qed.
Lemma lem3380690 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3380691 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term159 A B x f s) = (term63 A B x f s).
Proof. exact (MK_COMB (@lem3380690) (@lem3380689 A B x f s)). Qed.
Lemma lem3380692 {A B : Type'} (x : B) (f : A -> B) (a : A) : (term64 A B x f a) = (term64 A B x f a).
Proof. exact (eq_refl (term64 A B x f a)). Qed.
Lemma lem3380693 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term155 A B s x f a) = (term65 A B s x f a).
Proof. exact (MK_COMB (@lem3380691 A B x f s) (@lem3380692 A B x f a)). Qed.
Lemma lem3380694 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3380695 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term160 A B s x f a) = (term161 A B s x f a).
Proof. exact (MK_COMB (@lem3380694) (@lem3380693 A B s x f a)). Qed.
Lemma lem3380696 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term116 A B x f s x') = (term58 A B x f s x').
Proof. exact (eq_refl (term116 A B x f s x')). Qed.
Lemma lem3380697 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3380698 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term162 A B x f s x') = (term163 A B x f s x').
Proof. exact (MK_COMB (@lem3380697) (@lem3380696 A B x f s x')). Qed.
Lemma lem3380699 {A B : Type'} (x : B) (f : A -> B) (a : A) : (term64 A B x f a) = (term64 A B x f a).
Proof. exact (eq_refl (term64 A B x f a)). Qed.
Lemma lem3380700 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (a : A) : (term164 A B s x x' f a) = (term165 A B s x x' f a).
Proof. exact (MK_COMB (@lem3380698 A B x' f s x) (@lem3380699 A B x' f a)). Qed.
Lemma lem3380701 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term166 A B s x f a) = (term167 A B s x f a).
Proof. exact (fun_ext (fun x' : A => @lem3380700 A B s x' x f a)). Qed.
Lemma lem3380702 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3380703 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term156 A B s x f a) = (term168 A B s x f a).
Proof. exact (MK_COMB (@lem3380702 A) (@lem3380701 A B s x f a)). Qed.
Lemma lem3380704 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : ((term155 A B s x f a) = (term156 A B s x f a)) = ((term65 A B s x f a) = (term168 A B s x f a)).
Proof. exact (MK_COMB (@lem3380695 A B s x f a) (@lem3380703 A B s x f a)). Qed.
Lemma lem3380705 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term65 A B s x f a) = (term168 A B s x f a).
Proof. exact (EQ_MP (@lem3380704 A B s x f a) (@lem3380685 A B s x f a)). Qed.
Lemma lem3380706 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term128 A B x f s a) = (term128 A B x f s a).
Proof. exact (eq_refl (term128 A B x f s a)). Qed.
Lemma lem3380707 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term130 A B s x f a) = (term169 A B s x f a).
Proof. exact (MK_COMB (@lem3380706 A B x f s a) (@lem3380705 A B s x f a)). Qed.
Lemma lem3380709 {A : Type'} (P : Prop) (Q : A -> Prop) : (term170 A P Q) = (term171 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3380710 {A : Type'} (P : Prop) (Q : A -> Prop) : (term170 A P Q) = (term171 A P Q).
Proof. exact (@lem3380709 A P Q). Qed.
Lemma lem3380711 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term172 A B s x f a) = (term173 A B s x f a).
Proof. exact (@lem3380710 A (term111 A B x f s a) (term167 A B s x f a)). Qed.
Lemma lem3380712 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (a : A) : (term174 A B s x' f a x) = (term165 A B s x x' f a).
Proof. exact (eq_refl (term174 A B s x' f a x)). Qed.
Lemma lem3380713 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term175 A B s x f a) = (term167 A B s x f a).
Proof. exact (fun_ext (fun x' : A => @lem3380712 A B s x' x f a)). Qed.
Lemma lem3380714 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3380715 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term176 A B s x f a) = (term168 A B s x f a).
Proof. exact (MK_COMB (@lem3380714 A) (@lem3380713 A B s x f a)). Qed.
Lemma lem3380716 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term128 A B x f s a) = (term128 A B x f s a).
Proof. exact (eq_refl (term128 A B x f s a)). Qed.
Lemma lem3380717 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term172 A B s x f a) = (term169 A B s x f a).
Proof. exact (MK_COMB (@lem3380716 A B x f s a) (@lem3380715 A B s x f a)). Qed.
Lemma lem3380718 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3380719 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term177 A B s x f a) = (term178 A B s x f a).
Proof. exact (MK_COMB (@lem3380718) (@lem3380717 A B s x f a)). Qed.
Lemma lem3380720 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (a : A) : (term174 A B s x' f a x) = (term165 A B s x x' f a).
Proof. exact (eq_refl (term174 A B s x' f a x)). Qed.
Lemma lem3380721 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term128 A B x f s a) = (term128 A B x f s a).
Proof. exact (eq_refl (term128 A B x f s a)). Qed.
Lemma lem3380722 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (a : A) : (term179 A B s x' f a x) = (term180 A B s x x' f a).
Proof. exact (MK_COMB (@lem3380721 A B x' f s a) (@lem3380720 A B s x x' f a)). Qed.
Lemma lem3380723 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term181 A B s x f a) = (term182 A B s x f a).
Proof. exact (fun_ext (fun x' : A => @lem3380722 A B s x' x f a)). Qed.
Lemma lem3380724 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3380725 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term173 A B s x f a) = (term183 A B s x f a).
Proof. exact (MK_COMB (@lem3380724 A) (@lem3380723 A B s x f a)). Qed.
Lemma lem3380726 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : ((term172 A B s x f a) = (term173 A B s x f a)) = ((term169 A B s x f a) = (term183 A B s x f a)).
Proof. exact (MK_COMB (@lem3380719 A B s x f a) (@lem3380725 A B s x f a)). Qed.
Lemma lem3380727 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term169 A B s x f a) = (term183 A B s x f a).
Proof. exact (EQ_MP (@lem3380726 A B s x f a) (@lem3380711 A B s x f a)). Qed.
Lemma lem3380728 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term130 A B s x f a) = (term183 A B s x f a).
Proof. exact (TRANS (@lem3380707 A B s x f a) (@lem3380727 A B s x f a)). Qed.
Lemma lem3380729 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term137 A B s x f a) = (term184 A B s x f a).
Proof. exact (MK_COMB (@lem3380681 A B s x f a) (@lem3380728 A B s x f a)). Qed.
Lemma lem3380731 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term185 A P Q) = (term186 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3380732 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term185 A P Q) = (term186 A P Q).
Proof. exact (@lem3380731 A P Q). Qed.
Lemma lem3380733 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term187 A B s x f a) = (term188 A B s x f a).
Proof. exact (@lem3380732 A (term152 A B s x f a) (term182 A B s x f a)). Qed.
Lemma lem3380734 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (a : A) : (term189 A B s x' f a x) = (term150 A B x s x' f a).
Proof. exact (eq_refl (term189 A B s x' f a x)). Qed.
Lemma lem3380735 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term190 A B s x f a) = (term152 A B s x f a).
Proof. exact (fun_ext (fun x' : A => @lem3380734 A B x' s x f a)). Qed.
Lemma lem3380736 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3380737 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term191 A B s x f a) = (term153 A B s x f a).
Proof. exact (MK_COMB (@lem3380736 A) (@lem3380735 A B s x f a)). Qed.
Lemma lem3380738 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3380739 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term192 A B s x f a) = (term154 A B s x f a).
Proof. exact (MK_COMB (@lem3380738) (@lem3380737 A B s x f a)). Qed.
Lemma lem3380740 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (a : A) : (term193 A B s x' f a x) = (term180 A B s x x' f a).
Proof. exact (eq_refl (term193 A B s x' f a x)). Qed.
Lemma lem3380741 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term194 A B s x f a) = (term182 A B s x f a).
Proof. exact (fun_ext (fun x' : A => @lem3380740 A B s x' x f a)). Qed.
Lemma lem3380742 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3380743 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term195 A B s x f a) = (term183 A B s x f a).
Proof. exact (MK_COMB (@lem3380742 A) (@lem3380741 A B s x f a)). Qed.
Lemma lem3380744 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term187 A B s x f a) = (term184 A B s x f a).
Proof. exact (MK_COMB (@lem3380739 A B s x f a) (@lem3380743 A B s x f a)). Qed.
Lemma lem3380745 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3380746 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term196 A B s x f a) = (term197 A B s x f a).
Proof. exact (MK_COMB (@lem3380745) (@lem3380744 A B s x f a)). Qed.
Lemma lem3380747 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (a : A) : (term189 A B s x' f a x) = (term150 A B x s x' f a).
Proof. exact (eq_refl (term189 A B s x' f a x)). Qed.
Lemma lem3380748 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3380749 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (a : A) : (term198 A B s x' f a x) = (term199 A B x s x' f a).
Proof. exact (MK_COMB (@lem3380748) (@lem3380747 A B x s x' f a)). Qed.
Lemma lem3380750 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (a : A) : (term193 A B s x' f a x) = (term180 A B s x x' f a).
Proof. exact (eq_refl (term193 A B s x' f a x)). Qed.
Lemma lem3380751 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (a : A) : (term200 A B s x' f a x) = (term201 A B s x x' f a).
Proof. exact (MK_COMB (@lem3380749 A B x s x' f a) (@lem3380750 A B s x x' f a)). Qed.
Lemma lem3380752 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term202 A B s x f a) = (term203 A B s x f a).
Proof. exact (fun_ext (fun x' : A => @lem3380751 A B s x' x f a)). Qed.
Lemma lem3380753 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3380754 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term188 A B s x f a) = (term204 A B s x f a).
Proof. exact (MK_COMB (@lem3380753 A) (@lem3380752 A B s x f a)). Qed.
Lemma lem3380755 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : ((term187 A B s x f a) = (term188 A B s x f a)) = ((term184 A B s x f a) = (term204 A B s x f a)).
Proof. exact (MK_COMB (@lem3380746 A B s x f a) (@lem3380754 A B s x f a)). Qed.
Lemma lem3380756 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term184 A B s x f a) = (term204 A B s x f a).
Proof. exact (EQ_MP (@lem3380755 A B s x f a) (@lem3380733 A B s x f a)). Qed.
Lemma lem3380758 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term137 A B s x f a) = (term204 A B s x f a).
Proof. exact (TRANS (@lem3380729 A B s x f a) (@lem3380756 A B s x f a)). Qed.
Lemma lem3380759 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term85 A B s x f a) = (term204 A B s x f a).
Proof. exact (TRANS (@lem3380478 A B s x f a) (@lem3380758 A B s x f a)). Qed.
Lemma lem3380760 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term85 A B s x f a) : term204 A B s x f a.
Proof. exact (EQ_MP (@lem3380759 A B s x f a) (@lem3380324 A B s x f a h1)). Qed.
Lemma lem3380761 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term201 A B s x' x f a) : term201 A B s x' x f a.
Proof. exact (h1). Qed.
Lemma lem3380788 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (a : A) : (term91 A B s f x a) = (term91 A B s f x a).
Proof. exact (eq_refl (term91 A B s f x a)). Qed.
Lemma lem3380789 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term92 A B s f a) = (term92 A B s f a).
Proof. exact (fun_ext (fun x : A => @lem3380788 A B s f x a)). Qed.
Lemma lem3380790 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3380791 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term93 A B s f a) = (term93 A B s f a).
Proof. exact (MK_COMB (@lem3380790 A) (@lem3380789 A B s f a)). Qed.
Lemma lem3380792 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) (h1 : term37 A B s f a) : term93 A B s f a.
Proof. exact (EQ_MP (@lem3380791 A B s f a) (@lem3380393 A B s f a h1)). Qed.
Lemma lem3380817 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) : (term165 A B s x' x f a) = (term165 A B s x' x f a).
Proof. exact (eq_refl (term165 A B s x' x f a)). Qed.
Lemma lem3380842 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term101 A B x f s x' a) = (term101 A B x f s x' a).
Proof. exact (eq_refl (term101 A B x f s x' a)). Qed.
Lemma lem3380843 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term110 A B x f s a) = (term110 A B x f s a).
Proof. exact (fun_ext (fun x' : A => @lem3380842 A B x f s x' a)). Qed.
Lemma lem3380844 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3380845 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term111 A B x f s a) = (term111 A B x f s a).
Proof. exact (MK_COMB (@lem3380844 A) (@lem3380843 A B x f s a)). Qed.
Lemma lem3380846 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3380847 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term128 A B x f s a) = (term128 A B x f s a).
Proof. exact (MK_COMB (@lem3380846) (@lem3380845 A B x f s a)). Qed.
Lemma lem3380848 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) : (term180 A B s x' x f a) = (term180 A B s x' x f a).
Proof. exact (MK_COMB (@lem3380847 A B x f s a) (@lem3380817 A B s x' x f a)). Qed.
Lemma lem3380855 {A B : Type'} (x : B) (f : A -> B) (a : A) : (x = (f a)) = (x = (f a)).
Proof. exact (eq_refl (x = (f a))). Qed.
Lemma lem3380872 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term113 A B x f s x') = (term113 A B x f s x').
Proof. exact (eq_refl (term113 A B x f s x')). Qed.
Lemma lem3380873 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term119 A B x f s) = (term119 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3380872 A B x f s x')). Qed.
Lemma lem3380874 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3380875 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term120 A B x f s) = (term120 A B x f s).
Proof. exact (MK_COMB (@lem3380874 A) (@lem3380873 A B x f s)). Qed.
Lemma lem3380876 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3380877 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term123 A B x f s) = (term123 A B x f s).
Proof. exact (MK_COMB (@lem3380876) (@lem3380875 A B x f s)). Qed.
Lemma lem3380878 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term125 A B s x f a) = (term125 A B s x f a).
Proof. exact (MK_COMB (@lem3380877 A B x f s) (@lem3380855 A B x f a)). Qed.
Lemma lem3380903 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term148 A B x f s x' a) = (term148 A B x f s x' a).
Proof. exact (eq_refl (term148 A B x f s x' a)). Qed.
Lemma lem3380904 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term150 A B x' s x f a) = (term150 A B x' s x f a).
Proof. exact (MK_COMB (@lem3380903 A B x f s x' a) (@lem3380878 A B s x f a)). Qed.
Lemma lem3380905 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3380906 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) : (term199 A B x' s x f a) = (term199 A B x' s x f a).
Proof. exact (MK_COMB (@lem3380905) (@lem3380904 A B x' s x f a)). Qed.
Lemma lem3380907 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) : (term201 A B s x' x f a) = (term201 A B s x' x f a).
Proof. exact (MK_COMB (@lem3380906 A B x' s x f a) (@lem3380848 A B s x' x f a)). Qed.
Lemma lem3380908 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term201 A B s x' x f a) : term201 A B s x' x f a.
Proof. exact (EQ_MP (@lem3380907 A B s x' x f a) (@lem3380761 A B s x' x f a h1)). Qed.
Lemma lem3380909 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term150 A B x' s x f a) : term150 A B x' s x f a.
Proof. exact (h1). Qed.
Lemma lem3380910 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : term180 A B s x' x f a.
Proof. exact (h1). Qed.
Lemma lem3380911 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term150 A B x' s x f a) : term125 A B s x f a.
Proof. exact (proj2 (@lem3380909 A B x' s x f a h1)). Qed.
Lemma lem3380912 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term150 A B x' s x f a) : term49 A B x f s x' a.
Proof. exact (proj1 (@lem3380909 A B x' s x f a h1)). Qed.
Lemma lem3380913 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term150 A B x' s x f a) : term46 A s x' a.
Proof. exact (proj2 (@lem3380912 A B x' s x f a h1)). Qed.
Lemma lem3380917 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (h1 : term120 A B x f s) : term120 A B x f s.
Proof. exact (h1). Qed.
Lemma lem3380919 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : term165 A B s x' x f a.
Proof. exact (proj2 (@lem3380910 A B s x' x f a h1)). Qed.
Lemma lem3380920 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : term111 A B x f s a.
Proof. exact (proj1 (@lem3380910 A B s x' x f a h1)). Qed.
Lemma lem3380922 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : term58 A B x f s x'.
Proof. exact (proj1 (@lem3380919 A B s x' x f a h1)). Qed.
Lemma lem3380963 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term113 A B x f s x') = (term113 A B x f s x').
Proof. exact (eq_refl (term113 A B x f s x')). Qed.
Lemma lem3380964 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term119 A B x f s) = (term119 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3380963 A B x f s x')). Qed.
Lemma lem3380965 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3380967 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term120 A B x f s) = (term120 A B x f s).
Proof. exact (MK_COMB (@lem3380965 A) (@lem3380964 A B x f s)). Qed.
Lemma lem3380968 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (h1 : term120 A B x f s) : term120 A B x f s.
Proof. exact (EQ_MP (@lem3380967 A B x f s) (@lem3380917 A B x f s h1)). Qed.
Lemma lem3380982 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (a : A) : (term91 A B s f x a) = (term91 A B s f x a).
Proof. exact (eq_refl (term91 A B s f x a)). Qed.
Lemma lem3380983 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term92 A B s f a) = (term92 A B s f a).
Proof. exact (fun_ext (fun x : A => @lem3380982 A B s f x a)). Qed.
Lemma lem3380984 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3380986 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term93 A B s f a) = (term93 A B s f a).
Proof. exact (MK_COMB (@lem3380984 A) (@lem3380983 A B s f a)). Qed.
Lemma lem3380987 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) (h1 : term37 A B s f a) : term93 A B s f a.
Proof. exact (EQ_MP (@lem3380986 A B s f a) (@lem3380792 A B s f a h1)). Qed.
Lemma lem3381003 {A B : Type'} (x : B) (f : A -> B) (a : A) (h1 : x = (f a)) : x = (f a).
Proof. exact (h1). Qed.
Lemma lem3381036 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (a : A) : (term101 A B x f s x' a) = (term101 A B x f s x' a).
Proof. exact (eq_refl (term101 A B x f s x' a)). Qed.
Lemma lem3381037 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term110 A B x f s a) = (term110 A B x f s a).
Proof. exact (fun_ext (fun x' : A => @lem3381036 A B x f s x' a)). Qed.
Lemma lem3381038 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3381040 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (a : A) : (term111 A B x f s a) = (term111 A B x f s a).
Proof. exact (MK_COMB (@lem3381038 A) (@lem3381037 A B x f s a)). Qed.
Lemma lem3381041 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : term111 A B x f s a.
Proof. exact (EQ_MP (@lem3381040 A B x f s a) (@lem3380920 A B s x' x f a h1)). Qed.
Lemma lem3381057 {A B : Type'} (_35447 : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term120 A B x f s) : term205 A B x f s _35447.
Proof. exact (@lem3380968 A B x f s h1 _35447). Qed.
Lemma lem3381058 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_35447 : A) : (term205 A B x f s _35447) = (term113 A B x f s _35447).
Proof. exact (eq_refl (term205 A B x f s _35447)). Qed.
Lemma lem3381060 {A B : Type'} (_35448 : A) (s : A -> Prop) (f : A -> B) (a : A) (h1 : term37 A B s f a) : term206 A B s f a _35448.
Proof. exact (@lem3380987 A B s f a h1 _35448). Qed.
Lemma lem3381061 {A B : Type'} (s : A -> Prop) (f : A -> B) (_35448 : A) (a : A) : (term206 A B s f a _35448) = (term91 A B s f _35448 a).
Proof. exact (eq_refl (term206 A B s f a _35448)). Qed.
Lemma lem3381062 {A B : Type'} (_35448 : A) (s : A -> Prop) (f : A -> B) (a : A) (h1 : term37 A B s f a) : term91 A B s f _35448 a.
Proof. exact (EQ_MP (@lem3381061 A B s f _35448 a) (@lem3381060 A B _35448 s f a h1)). Qed.
Lemma lem3381066 {A B : Type'} (_35450 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : term207 A B x f s a _35450.
Proof. exact (@lem3381041 A B s x' x f a h1 _35450). Qed.
Lemma lem3381067 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_35450 : A) (a : A) : (term207 A B x f s a _35450) = (term101 A B x f s _35450 a).
Proof. exact (eq_refl (term207 A B x f s a _35450)). Qed.
Lemma lem3381082 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term150 A B x' s x f a) : x = (f x').
Proof. exact (proj1 (@lem3380912 A B x' s x f a h1)). Qed.
Lemma lem3381092 {A B : Type'} (_35447 : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term120 A B x f s) : term113 A B x f s _35447.
Proof. exact (EQ_MP (@lem3381058 A B x f s _35447) (@lem3381057 A B _35447 x f s h1)). Qed.
Lemma lem3381103 {A B : Type'} (s : A -> Prop) (f : A -> B) (_35448 : A) (a : A) : (term91 A B s f _35448 a) = (term208 A B s f _35448 a).
Proof. exact (@lem3379804 (term209 A s _35448) (term210 A B _35448 f a) (_35448 = a)). Qed.
Lemma lem3381106 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term150 A B x' s x f a) : x = (f x').
Proof. exact (proj1 (@lem3380912 A B x' s x f a h1)). Qed.
Lemma lem3381112 {A B : Type'} (x : B) (f : A -> B) (a : A) (h1 : x = (f a)) : x = (f a).
Proof. exact (h1). Qed.
Lemma lem3381134 {A B : Type'} (_35450 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : term101 A B x f s _35450 a.
Proof. exact (EQ_MP (@lem3381067 A B x f s _35450 a) (@lem3381066 A B _35450 s x' x f a h1)). Qed.
Lemma lem3381136 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : term64 A B x f a.
Proof. exact (proj2 (@lem3380919 A B s x' x f a h1)). Qed.
Lemma lem3381138 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : x = (f x').
Proof. exact (proj1 (@lem3380922 A B s x' x f a h1)). Qed.
Lemma lem3381197 {A B : Type'} (f : A -> B) (s : A -> Prop) (_35447 : A) : (term211 A B f s _35447) = (term211 A B f s _35447).
Proof. exact (eq_refl (term211 A B f s _35447)). Qed.
Lemma lem3381198 {A B : Type'} (_35447 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term150 A B x' s x f a) : (term212 A B f s _35447 x) = (term213 A B s _35447 f x').
Proof. exact (MK_COMB (@lem3381197 A B f s _35447) (@lem3381082 A B x' s x f a h1)). Qed.
Lemma lem3381199 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35447 : A) : (term213 A B s _35447 f x') = (term214 A B x' f s _35447).
Proof. exact (eq_refl (term213 A B s _35447 f x')). Qed.
Lemma lem3381200 {A B : Type'} (f : A -> B) (s : A -> Prop) (_35447 : A) (x : B) : (term215 A B f s _35447 x) = (term215 A B f s _35447 x).
Proof. exact (eq_refl (term215 A B f s _35447 x)). Qed.
Lemma lem3381201 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_35447 : A) : ((term212 A B f s _35447 x) = (term213 A B s _35447 f x')) = ((term212 A B f s _35447 x) = (term214 A B x' f s _35447)).
Proof. exact (MK_COMB (@lem3381200 A B f s _35447 x) (@lem3381199 A B x' f s _35447)). Qed.
Lemma lem3381202 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_35447 : A) : (term212 A B f s _35447 x) = (term113 A B x f s _35447).
Proof. exact (eq_refl (term212 A B f s _35447 x)). Qed.
Lemma lem3381203 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3381204 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_35447 : A) : (term215 A B f s _35447 x) = (term216 A B x f s _35447).
Proof. exact (MK_COMB (@lem3381203) (@lem3381202 A B x f s _35447)). Qed.
Lemma lem3381205 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35447 : A) : (term214 A B x' f s _35447) = (term214 A B x' f s _35447).
Proof. exact (eq_refl (term214 A B x' f s _35447)). Qed.
Lemma lem3381206 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_35447 : A) : ((term212 A B f s _35447 x) = (term214 A B x' f s _35447)) = ((term113 A B x f s _35447) = (term214 A B x' f s _35447)).
Proof. exact (MK_COMB (@lem3381204 A B x f s _35447) (@lem3381205 A B x' f s _35447)). Qed.
Lemma lem3381207 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_35447 : A) : ((term212 A B f s _35447 x) = (term213 A B s _35447 f x')) = ((term113 A B x f s _35447) = (term214 A B x' f s _35447)).
Proof. exact (TRANS (@lem3381201 A B x x' f s _35447) (@lem3381206 A B x x' f s _35447)). Qed.
Lemma lem3381208 {A B : Type'} (_35447 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term150 A B x' s x f a) : (term113 A B x f s _35447) = (term214 A B x' f s _35447).
Proof. exact (EQ_MP (@lem3381207 A B x x' f s _35447) (@lem3381198 A B _35447 x' s x f a h1)). Qed.
Lemma lem3381209 {A B : Type'} (_35447 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term120 A B x f s) (h2 : term150 A B x' s x f a) : term214 A B x' f s _35447.
Proof. exact (EQ_MP (@lem3381208 A B _35447 x' s x f a h2) (@lem3381092 A B _35447 x f s h1)). Qed.
Lemma lem3381237 {A B : Type'} (_35448 : A) (s : A -> Prop) (f : A -> B) (a : A) (h1 : term37 A B s f a) : term208 A B s f _35448 a.
Proof. exact (EQ_MP (@lem3381103 A B s f _35448 a) (@lem3381062 A B _35448 s f a h1)). Qed.
Lemma lem3381238 {A B : Type'} (f : A -> B) (x' : A) : (term217 A B f x') = (term217 A B f x').
Proof. exact (eq_refl (term217 A B f x')). Qed.
Lemma lem3381239 {A B : Type'} (x' : A) (x : B) (f : A -> B) (a : A) (h1 : x = (f a)) : (term218 A B f x' x) = (term219 A B x' f a).
Proof. exact (MK_COMB (@lem3381238 A B f x') (@lem3381112 A B x f a h1)). Qed.
Lemma lem3381240 {A B : Type'} (a : A) (f : A -> B) (x' : A) : (term219 A B x' f a) = ((f a) = (f x')).
Proof. exact (eq_refl (term219 A B x' f a)). Qed.
Lemma lem3381241 {A B : Type'} (f : A -> B) (x' : A) (x : B) : (term220 A B f x' x) = (term220 A B f x' x).
Proof. exact (eq_refl (term220 A B f x' x)). Qed.
Lemma lem3381242 {A B : Type'} (x : B) (a : A) (f : A -> B) (x' : A) : ((term218 A B f x' x) = (term219 A B x' f a)) = ((term218 A B f x' x) = ((f a) = (f x'))).
Proof. exact (MK_COMB (@lem3381241 A B f x' x) (@lem3381240 A B a f x')). Qed.
Lemma lem3381243 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term218 A B f x' x) = (x = (f x')).
Proof. exact (eq_refl (term218 A B f x' x)). Qed.
Lemma lem3381244 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3381245 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term220 A B f x' x) = (term221 A B x f x').
Proof. exact (MK_COMB (@lem3381244) (@lem3381243 A B x f x')). Qed.
Lemma lem3381246 {A B : Type'} (a : A) (f : A -> B) (x' : A) : ((f a) = (f x')) = ((f a) = (f x')).
Proof. exact (eq_refl ((f a) = (f x'))). Qed.
Lemma lem3381247 {A B : Type'} (x : B) (a : A) (f : A -> B) (x' : A) : ((term218 A B f x' x) = ((f a) = (f x'))) = ((x = (f x')) = ((f a) = (f x'))).
Proof. exact (MK_COMB (@lem3381245 A B x f x') (@lem3381246 A B a f x')). Qed.
Lemma lem3381248 {A B : Type'} (x : B) (a : A) (f : A -> B) (x' : A) : ((term218 A B f x' x) = (term219 A B x' f a)) = ((x = (f x')) = ((f a) = (f x'))).
Proof. exact (TRANS (@lem3381242 A B x a f x') (@lem3381247 A B x a f x')). Qed.
Lemma lem3381249 {A B : Type'} (x' : A) (x : B) (f : A -> B) (a : A) (h1 : x = (f a)) : (x = (f x')) = ((f a) = (f x')).
Proof. exact (EQ_MP (@lem3381248 A B x a f x') (@lem3381239 A B x' x f a h1)). Qed.
Lemma lem3381278 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term150 A B x' s x f a) : term45 A x' a.
Proof. exact (proj2 (@lem3380913 A B x' s x f a h1)). Qed.
Lemma lem3381307 {A B : Type'} (f : A -> B) (s : A -> Prop) (_35450 : A) (a : A) : (term222 A B f s _35450 a) = (term222 A B f s _35450 a).
Proof. exact (eq_refl (term222 A B f s _35450 a)). Qed.
Lemma lem3381308 {A B : Type'} (_35450 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : (term223 A B f s _35450 a x) = (term224 A B s _35450 a f x').
Proof. exact (MK_COMB (@lem3381307 A B f s _35450 a) (@lem3381138 A B s x' x f a h1)). Qed.
Lemma lem3381309 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35450 : A) (a : A) : (term224 A B s _35450 a f x') = (term225 A B x' f s _35450 a).
Proof. exact (eq_refl (term224 A B s _35450 a f x')). Qed.
Lemma lem3381310 {A B : Type'} (f : A -> B) (s : A -> Prop) (_35450 : A) (a : A) (x : B) : (term226 A B f s _35450 a x) = (term226 A B f s _35450 a x).
Proof. exact (eq_refl (term226 A B f s _35450 a x)). Qed.
Lemma lem3381311 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_35450 : A) (a : A) : ((term223 A B f s _35450 a x) = (term224 A B s _35450 a f x')) = ((term223 A B f s _35450 a x) = (term225 A B x' f s _35450 a)).
Proof. exact (MK_COMB (@lem3381310 A B f s _35450 a x) (@lem3381309 A B x' f s _35450 a)). Qed.
Lemma lem3381312 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_35450 : A) (a : A) : (term223 A B f s _35450 a x) = (term101 A B x f s _35450 a).
Proof. exact (eq_refl (term223 A B f s _35450 a x)). Qed.
Lemma lem3381313 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3381314 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_35450 : A) (a : A) : (term226 A B f s _35450 a x) = (term227 A B x f s _35450 a).
Proof. exact (MK_COMB (@lem3381313) (@lem3381312 A B x f s _35450 a)). Qed.
Lemma lem3381315 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35450 : A) (a : A) : (term225 A B x' f s _35450 a) = (term225 A B x' f s _35450 a).
Proof. exact (eq_refl (term225 A B x' f s _35450 a)). Qed.
Lemma lem3381316 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_35450 : A) (a : A) : ((term223 A B f s _35450 a x) = (term225 A B x' f s _35450 a)) = ((term101 A B x f s _35450 a) = (term225 A B x' f s _35450 a)).
Proof. exact (MK_COMB (@lem3381314 A B x f s _35450 a) (@lem3381315 A B x' f s _35450 a)). Qed.
Lemma lem3381317 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_35450 : A) (a : A) : ((term223 A B f s _35450 a x) = (term224 A B s _35450 a f x')) = ((term101 A B x f s _35450 a) = (term225 A B x' f s _35450 a)).
Proof. exact (TRANS (@lem3381311 A B x x' f s _35450 a) (@lem3381316 A B x x' f s _35450 a)). Qed.
Lemma lem3381318 {A B : Type'} (_35450 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : (term101 A B x f s _35450 a) = (term225 A B x' f s _35450 a).
Proof. exact (EQ_MP (@lem3381317 A B x x' f s _35450 a) (@lem3381308 A B _35450 s x' x f a h1)). Qed.
Lemma lem3381319 {A B : Type'} (_35450 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : term225 A B x' f s _35450 a.
Proof. exact (EQ_MP (@lem3381318 A B _35450 s x' x f a h1) (@lem3381134 A B _35450 s x' x f a h1)). Qed.
Lemma lem3381320 {A B : Type'} (f : A -> B) (a : A) : (term228 A B f a) = (term228 A B f a).
Proof. exact (eq_refl (term228 A B f a)). Qed.
Lemma lem3381321 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : (term229 A B f a x) = (term230 A B a f x').
Proof. exact (MK_COMB (@lem3381320 A B f a) (@lem3381138 A B s x' x f a h1)). Qed.
Lemma lem3381322 {A B : Type'} (x' : A) (f : A -> B) (a : A) : (term230 A B a f x') = (term210 A B x' f a).
Proof. exact (eq_refl (term230 A B a f x')). Qed.
Lemma lem3381323 {A B : Type'} (f : A -> B) (a : A) (x : B) : (term231 A B f a x) = (term231 A B f a x).
Proof. exact (eq_refl (term231 A B f a x)). Qed.
Lemma lem3381324 {A B : Type'} (x : B) (x' : A) (f : A -> B) (a : A) : ((term229 A B f a x) = (term230 A B a f x')) = ((term229 A B f a x) = (term210 A B x' f a)).
Proof. exact (MK_COMB (@lem3381323 A B f a x) (@lem3381322 A B x' f a)). Qed.
Lemma lem3381325 {A B : Type'} (x : B) (f : A -> B) (a : A) : (term229 A B f a x) = (term64 A B x f a).
Proof. exact (eq_refl (term229 A B f a x)). Qed.
Lemma lem3381326 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3381327 {A B : Type'} (x : B) (f : A -> B) (a : A) : (term231 A B f a x) = (term232 A B x f a).
Proof. exact (MK_COMB (@lem3381326) (@lem3381325 A B x f a)). Qed.
Lemma lem3381328 {A B : Type'} (x' : A) (f : A -> B) (a : A) : (term210 A B x' f a) = (term210 A B x' f a).
Proof. exact (eq_refl (term210 A B x' f a)). Qed.
Lemma lem3381329 {A B : Type'} (x : B) (x' : A) (f : A -> B) (a : A) : ((term229 A B f a x) = (term210 A B x' f a)) = ((term64 A B x f a) = (term210 A B x' f a)).
Proof. exact (MK_COMB (@lem3381327 A B x f a) (@lem3381328 A B x' f a)). Qed.
Lemma lem3381330 {A B : Type'} (x : B) (x' : A) (f : A -> B) (a : A) : ((term229 A B f a x) = (term230 A B a f x')) = ((term64 A B x f a) = (term210 A B x' f a)).
Proof. exact (TRANS (@lem3381324 A B x x' f a) (@lem3381329 A B x x' f a)). Qed.
Lemma lem3381331 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : (term64 A B x f a) = (term210 A B x' f a).
Proof. exact (EQ_MP (@lem3381330 A B x x' f a) (@lem3381321 A B s x' x f a h1)). Qed.
Lemma lem3381332 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : term210 A B x' f a.
Proof. exact (EQ_MP (@lem3381331 A B s x' x f a h1) (@lem3381136 A B s x' x f a h1)). Qed.
Lemma lem3381372 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3381373 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3381372 B x). Qed.
Lemma lem3381374 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem3381373 B (f x')). Qed.
Lemma lem3381375 {A B : Type'} (f : A -> B) (x' : A) : term233 A B f x'.
Proof. exact (fun h0 : term234 A B f x' => @lem3381374 A B f x'). Qed.
Lemma lem3381377 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3381378 {A B : Type'} (f : A -> B) (x' : A) : (term233 A B f x') = ((f x') = (f x')).
Proof. exact (@lem3381377 ((f x') = (f x'))). Qed.
Lemma lem3381379 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3381378 A B f x') (@lem3381375 A B f x')). Qed.
Lemma lem3381381 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term150 A B x' s x f a) : s x'.
Proof. exact (proj1 (@lem3380913 A B x' s x f a h1)). Qed.
Lemma lem3381382 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term150 A B x' s x f a) : term236 A s x'.
Proof. exact (fun h0 : term209 A s x' => @lem3381381 A B x' s x f a h1). Qed.
Lemma lem3381384 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3381385 {A : Type'} (s : A -> Prop) (x' : A) : (term236 A s x') = (s x').
Proof. exact (@lem3381384 (s x')). Qed.
Lemma lem3381386 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term150 A B x' s x f a) : s x'.
Proof. exact (EQ_MP (@lem3381385 A s x') (@lem3381382 A B x' s x f a h1)). Qed.
Lemma lem3381388 (a : Prop) (b : Prop) : (term237 a b) = (term238 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3381389 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35447 : A) : (term214 A B x' f s _35447) = (term239 A B x' f s _35447).
Proof. exact (@lem3381388 ((f x') = (f _35447)) (s _35447)). Qed.
Lemma lem3381391 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3381392 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35447 : A) : (term239 A B x' f s _35447) = (term240 A B x' f s _35447).
Proof. exact (@lem3381391 (term241 A B x' f s _35447)). Qed.
Lemma lem3381393 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35447 : A) : (term214 A B x' f s _35447) = (term240 A B x' f s _35447).
Proof. exact (TRANS (@lem3381389 A B x' f s _35447) (@lem3381392 A B x' f s _35447)). Qed.
Lemma lem3381395 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term150 A B x' s x f a) : term242 A B f s x'.
Proof. exact (conj (@lem3381379 A B f x') (@lem3381386 A B x' s x f a h1)). Qed.
Lemma lem3381397 {A B : Type'} (_35447 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term120 A B x f s) (h2 : term150 A B x' s x f a) : term240 A B x' f s _35447.
Proof. exact (EQ_MP (@lem3381393 A B x' f s _35447) (@lem3381209 A B _35447 x' s x f a h1 h2)). Qed.
Lemma lem3381398 {A B : Type'} (_35447 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term120 A B x f s) (h2 : term150 A B x' s x f a) : term240 A B x' f s _35447.
Proof. exact (@lem3381397 A B _35447 x' s x f a h1 h2). Qed.
Lemma lem3381399 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term120 A B x f s) (h2 : term150 A B x' s x f a) : term243 A B f s x'.
Proof. exact (@lem3381398 A B x' x' s x f a h1 h2). Qed.
Lemma lem3381402 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term120 A B x f s) (h2 : term150 A B x' s x f a) : False.
Proof. exact (@lem3381399 A B x' s x f a h1 h2 (@lem3381395 A B x' s x f a h2)). Qed.
Lemma lem3381403 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term120 A B x f s) (h2 : term150 A B x' s x f a) : term244.
Proof. exact (fun h0 : ~ False => @lem3381402 A B x' s x f a h1 h2). Qed.
Lemma lem3381405 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3381406 : term244 = False.
Proof. exact (@lem3381405 False). Qed.
Lemma lem3381429 {B : Type'} (x : B) (y : B) (z : B) : term245 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem3381433 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term150 A B x' s x f a) : s x'.
Proof. exact (proj1 (@lem3380913 A B x' s x f a h1)). Qed.
Lemma lem3381434 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term150 A B x' s x f a) : term236 A s x'.
Proof. exact (fun h0 : term209 A s x' => @lem3381433 A B x' s x f a h1). Qed.
Lemma lem3381436 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3381437 {A : Type'} (s : A -> Prop) (x' : A) : (term236 A s x') = (s x').
Proof. exact (@lem3381436 (s x')). Qed.
Lemma lem3381438 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term150 A B x' s x f a) : s x'.
Proof. exact (EQ_MP (@lem3381437 A s x') (@lem3381434 A B x' s x f a h1)). Qed.
Lemma lem3381440 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term150 A B x' s x f a) (h2 : x = (f a)) : (f a) = (f x').
Proof. exact (EQ_MP (@lem3381249 A B x' x f a h2) (@lem3381106 A B x' s x f a h1)). Qed.
Lemma lem3381441 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term150 A B x' s x f a) (h2 : x = (f a)) : term246 A B a f x'.
Proof. exact (fun h0 : term210 A B a f x' => @lem3381440 A B x' s x f a h1 h2). Qed.
Lemma lem3381443 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3381444 {A B : Type'} (a : A) (f : A -> B) (x' : A) : (term246 A B a f x') = ((f a) = (f x')).
Proof. exact (@lem3381443 ((f a) = (f x'))). Qed.
Lemma lem3381445 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term150 A B x' s x f a) (h2 : x = (f a)) : (f a) = (f x').
Proof. exact (EQ_MP (@lem3381444 A B a f x') (@lem3381441 A B x' s x f a h1 h2)). Qed.
Lemma lem3381447 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3381448 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3381447 B x). Qed.
Lemma lem3381449 {A B : Type'} (f : A -> B) (a : A) : (f a) = (f a).
Proof. exact (@lem3381448 B (f a)). Qed.
Lemma lem3381450 {A B : Type'} (f : A -> B) (a : A) : term233 A B f a.
Proof. exact (fun h0 : term234 A B f a => @lem3381449 A B f a). Qed.
Lemma lem3381452 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3381453 {A B : Type'} (f : A -> B) (a : A) : (term233 A B f a) = ((f a) = (f a)).
Proof. exact (@lem3381452 ((f a) = (f a))). Qed.
Lemma lem3381454 {A B : Type'} (f : A -> B) (a : A) : (f a) = (f a).
Proof. exact (EQ_MP (@lem3381453 A B f a) (@lem3381450 A B f a)). Qed.
Lemma lem3381472 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3381473 {B : Type'} (y : B) (x : B) (z : B) : (term247 B x y z) = (term248 B y x z).
Proof. exact (@lem3381472 (y = z) (term45 B x z)). Qed.
Lemma lem3381483 {B : Type'} (x : B) (y : B) : (term249 B x y) = (term249 B x y).
Proof. exact (eq_refl (term249 B x y)). Qed.
Lemma lem3381484 {B : Type'} (y : B) (x : B) (z : B) : (term245 B x y z) = (term250 B y x z).
Proof. exact (MK_COMB (@lem3381483 B x y) (@lem3381473 B y x z)). Qed.
Lemma lem3381488 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3381489 {B : Type'} (y : B) (x : B) (z : B) : (term250 B y x z) = (term251 B y x z).
Proof. exact (@lem3381488 (y = z) (term45 B x y) (term45 B x z)). Qed.
Lemma lem3381511 {B : Type'} (y : B) (x : B) (z : B) : (term245 B x y z) = (term251 B y x z).
Proof. exact (TRANS (@lem3381484 B y x z) (@lem3381489 B y x z)). Qed.
Lemma lem3381512 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3381513 {B : Type'} (y : B) (x : B) (z : B) : (term252 B x y z) = (term253 B y x z).
Proof. exact (MK_COMB (@lem3381512) (@lem3381511 B y x z)). Qed.
Lemma lem3381535 {B : Type'} (y : B) (x : B) (z : B) : (term251 B y x z) = (term251 B y x z).
Proof. exact (eq_refl (term251 B y x z)). Qed.
Lemma lem3381536 {B : Type'} (y : B) (x : B) (z : B) : ((term245 B x y z) = (term251 B y x z)) = ((term251 B y x z) = (term251 B y x z)).
Proof. exact (MK_COMB (@lem3381513 B y x z) (@lem3381535 B y x z)). Qed.
Lemma lem3381538 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3381539 (x : Prop) : (x = x) = True.
Proof. exact (@lem3381538 Prop x). Qed.
Lemma lem3381540 {B : Type'} (y : B) (x : B) (z : B) : ((term251 B y x z) = (term251 B y x z)) = True.
Proof. exact (@lem3381539 (term251 B y x z)). Qed.
Lemma lem3381541 {B : Type'} (y : B) (x : B) (z : B) : ((term245 B x y z) = (term251 B y x z)) = True.
Proof. exact (TRANS (@lem3381536 B y x z) (@lem3381540 B y x z)). Qed.
Lemma lem3381542 {B : Type'} (y : B) (x : B) (z : B) : True = ((term245 B x y z) = (term251 B y x z)).
Proof. exact (SYM (@lem3381541 B y x z)). Qed.
Lemma lem3381543 {B : Type'} (y : B) (x : B) (z : B) : (term245 B x y z) = (term251 B y x z).
Proof. exact (EQ_MP (@lem3381542 B y x z) (@lem0)). Qed.
Lemma lem3381544 {B : Type'} (y : B) (x : B) (z : B) : term251 B y x z.
Proof. exact (EQ_MP (@lem3381543 B y x z) (@lem3381429 B x y z)). Qed.
Lemma lem3381546 (b : Prop) (a : Prop) : (a \/ b) = (term254 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3381547 {B : Type'} (x : B) (y : B) (z : B) : (term251 B y x z) = (term255 B x y z).
Proof. exact (@lem3381546 (term256 B y x z) (y = z)). Qed.
Lemma lem3381549 (a : Prop) (b : Prop) : (term257 a b) = (term258 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3381550 {B : Type'} (y : B) (x : B) (z : B) : (term259 B y x z) = (term260 B y x z).
Proof. exact (@lem3381549 (term45 B x y) (term45 B x z)). Qed.
Lemma lem3381552 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3381553 {B : Type'} (x : B) (y : B) : (term94 B x y) = (x = y).
Proof. exact (@lem3381552 (x = y)). Qed.
Lemma lem3381554 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3381555 {B : Type'} (x : B) (y : B) : (term261 B x y) = (term262 B x y).
Proof. exact (MK_COMB (@lem3381554) (@lem3381553 B x y)). Qed.
Lemma lem3381557 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3381558 {B : Type'} (x : B) (z : B) : (term94 B x z) = (x = z).
Proof. exact (@lem3381557 (x = z)). Qed.
Lemma lem3381559 {B : Type'} (y : B) (x : B) (z : B) : (term260 B y x z) = (term263 B y x z).
Proof. exact (MK_COMB (@lem3381555 B x y) (@lem3381558 B x z)). Qed.
Lemma lem3381560 {B : Type'} (y : B) (x : B) (z : B) : (term259 B y x z) = (term263 B y x z).
Proof. exact (TRANS (@lem3381550 B y x z) (@lem3381559 B y x z)). Qed.
Lemma lem3381561 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3381562 {B : Type'} (y : B) (x : B) (z : B) : (term264 B y x z) = (term265 B y x z).
Proof. exact (MK_COMB (@lem3381561) (@lem3381560 B y x z)). Qed.
Lemma lem3381563 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3381564 {B : Type'} (x : B) (y : B) (z : B) : (term255 B x y z) = (term266 B x y z).
Proof. exact (MK_COMB (@lem3381562 B y x z) (@lem3381563 B y z)). Qed.
Lemma lem3381565 {B : Type'} (x : B) (y : B) (z : B) : (term251 B y x z) = (term266 B x y z).
Proof. exact (TRANS (@lem3381547 B x y z) (@lem3381564 B x y z)). Qed.
Lemma lem3381567 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term150 A B x' s x f a) (h2 : x = (f a)) : term267 A B x' f a.
Proof. exact (conj (@lem3381445 A B x' s x f a h1 h2) (@lem3381454 A B f a)). Qed.
Lemma lem3381569 {B : Type'} (x : B) (y : B) (z : B) : term266 B x y z.
Proof. exact (EQ_MP (@lem3381565 B x y z) (@lem3381544 B y x z)). Qed.
Lemma lem3381570 {B : Type'} (x : B) (y : B) (z : B) : term266 B x y z.
Proof. exact (@lem3381569 B x y z). Qed.
Lemma lem3381571 {A B : Type'} (x' : A) (f : A -> B) (a : A) : term268 A B x' f a.
Proof. exact (@lem3381570 B (f a) (f x') (f a)). Qed.
Lemma lem3381574 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term150 A B x' s x f a) (h2 : x = (f a)) : (f x') = (f a).
Proof. exact (@lem3381571 A B x' f a (@lem3381567 A B x' s x f a h1 h2)). Qed.
Lemma lem3381575 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term150 A B x' s x f a) (h2 : x = (f a)) : term246 A B x' f a.
Proof. exact (fun h0 : term210 A B x' f a => @lem3381574 A B x' s x f a h1 h2). Qed.
Lemma lem3381577 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3381578 {A B : Type'} (x' : A) (f : A -> B) (a : A) : (term246 A B x' f a) = ((f x') = (f a)).
Proof. exact (@lem3381577 ((f x') = (f a))). Qed.
Lemma lem3381579 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term150 A B x' s x f a) (h2 : x = (f a)) : (f x') = (f a).
Proof. exact (EQ_MP (@lem3381578 A B x' f a) (@lem3381575 A B x' s x f a h1 h2)). Qed.
Lemma lem3381595 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3381596 {A B : Type'} (_35448 : A) (f : A -> B) (a : A) : (term269 A B f _35448 a) = (term270 A B _35448 f a).
Proof. exact (@lem3381595 (_35448 = a) (term210 A B _35448 f a)). Qed.
Lemma lem3381606 {A : Type'} (s : A -> Prop) (_35448 : A) : (term95 A s _35448) = (term95 A s _35448).
Proof. exact (eq_refl (term95 A s _35448)). Qed.
Lemma lem3381607 {A B : Type'} (s : A -> Prop) (_35448 : A) (f : A -> B) (a : A) : (term208 A B s f _35448 a) = (term271 A B s _35448 f a).
Proof. exact (MK_COMB (@lem3381606 A s _35448) (@lem3381596 A B _35448 f a)). Qed.
Lemma lem3381611 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3381612 {A B : Type'} (s : A -> Prop) (_35448 : A) (f : A -> B) (a : A) : (term271 A B s _35448 f a) = (term272 A B s _35448 f a).
Proof. exact (@lem3381611 (_35448 = a) (term209 A s _35448) (term210 A B _35448 f a)). Qed.
Lemma lem3381632 {A B : Type'} (s : A -> Prop) (_35448 : A) (f : A -> B) (a : A) : (term208 A B s f _35448 a) = (term272 A B s _35448 f a).
Proof. exact (TRANS (@lem3381607 A B s _35448 f a) (@lem3381612 A B s _35448 f a)). Qed.
Lemma lem3381633 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3381634 {A B : Type'} (s : A -> Prop) (_35448 : A) (f : A -> B) (a : A) : (term273 A B s f _35448 a) = (term274 A B s _35448 f a).
Proof. exact (MK_COMB (@lem3381633) (@lem3381632 A B s _35448 f a)). Qed.
Lemma lem3381654 {A B : Type'} (s : A -> Prop) (_35448 : A) (f : A -> B) (a : A) : (term272 A B s _35448 f a) = (term272 A B s _35448 f a).
Proof. exact (eq_refl (term272 A B s _35448 f a)). Qed.
Lemma lem3381655 {A B : Type'} (s : A -> Prop) (_35448 : A) (f : A -> B) (a : A) : ((term208 A B s f _35448 a) = (term272 A B s _35448 f a)) = ((term272 A B s _35448 f a) = (term272 A B s _35448 f a)).
Proof. exact (MK_COMB (@lem3381634 A B s _35448 f a) (@lem3381654 A B s _35448 f a)). Qed.
Lemma lem3381657 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3381658 (x : Prop) : (x = x) = True.
Proof. exact (@lem3381657 Prop x). Qed.
Lemma lem3381659 {A B : Type'} (s : A -> Prop) (_35448 : A) (f : A -> B) (a : A) : ((term272 A B s _35448 f a) = (term272 A B s _35448 f a)) = True.
Proof. exact (@lem3381658 (term272 A B s _35448 f a)). Qed.
Lemma lem3381660 {A B : Type'} (s : A -> Prop) (_35448 : A) (f : A -> B) (a : A) : ((term208 A B s f _35448 a) = (term272 A B s _35448 f a)) = True.
Proof. exact (TRANS (@lem3381655 A B s _35448 f a) (@lem3381659 A B s _35448 f a)). Qed.
Lemma lem3381661 {A B : Type'} (s : A -> Prop) (_35448 : A) (f : A -> B) (a : A) : True = ((term208 A B s f _35448 a) = (term272 A B s _35448 f a)).
Proof. exact (SYM (@lem3381660 A B s _35448 f a)). Qed.
Lemma lem3381662 {A B : Type'} (s : A -> Prop) (_35448 : A) (f : A -> B) (a : A) : (term208 A B s f _35448 a) = (term272 A B s _35448 f a).
Proof. exact (EQ_MP (@lem3381661 A B s _35448 f a) (@lem0)). Qed.
Lemma lem3381663 {A B : Type'} (_35448 : A) (s : A -> Prop) (f : A -> B) (a : A) (h1 : term37 A B s f a) : term272 A B s _35448 f a.
Proof. exact (EQ_MP (@lem3381662 A B s _35448 f a) (@lem3381237 A B _35448 s f a h1)). Qed.
Lemma lem3381665 (b : Prop) (a : Prop) : (a \/ b) = (term254 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3381666 {A B : Type'} (s : A -> Prop) (f : A -> B) (_35448 : A) (a : A) : (term272 A B s _35448 f a) = (term275 A B s f _35448 a).
Proof. exact (@lem3381665 (term87 A B s _35448 f a) (_35448 = a)). Qed.
Lemma lem3381668 (a : Prop) (b : Prop) : (term257 a b) = (term258 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3381669 {A B : Type'} (s : A -> Prop) (_35448 : A) (f : A -> B) (a : A) : (term276 A B s _35448 f a) = (term277 A B s _35448 f a).
Proof. exact (@lem3381668 (term209 A s _35448) (term210 A B _35448 f a)). Qed.
Lemma lem3381671 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3381672 {A : Type'} (s : A -> Prop) (_35448 : A) : (term278 A s _35448) = (s _35448).
Proof. exact (@lem3381671 (s _35448)). Qed.
Lemma lem3381673 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3381674 {A : Type'} (s : A -> Prop) (_35448 : A) : (term279 A s _35448) = (term27 A s _35448).
Proof. exact (MK_COMB (@lem3381673) (@lem3381672 A s _35448)). Qed.
Lemma lem3381676 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3381677 {A B : Type'} (_35448 : A) (f : A -> B) (a : A) : (term280 A B _35448 f a) = ((f _35448) = (f a)).
Proof. exact (@lem3381676 ((f _35448) = (f a))). Qed.
Lemma lem3381678 {A B : Type'} (s : A -> Prop) (_35448 : A) (f : A -> B) (a : A) : (term277 A B s _35448 f a) = (term29 A B s _35448 f a).
Proof. exact (MK_COMB (@lem3381674 A s _35448) (@lem3381677 A B _35448 f a)). Qed.
Lemma lem3381679 {A B : Type'} (s : A -> Prop) (_35448 : A) (f : A -> B) (a : A) : (term276 A B s _35448 f a) = (term29 A B s _35448 f a).
Proof. exact (TRANS (@lem3381669 A B s _35448 f a) (@lem3381678 A B s _35448 f a)). Qed.
Lemma lem3381680 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3381681 {A B : Type'} (s : A -> Prop) (_35448 : A) (f : A -> B) (a : A) : (term281 A B s _35448 f a) = (term31 A B s _35448 f a).
Proof. exact (MK_COMB (@lem3381680) (@lem3381679 A B s _35448 f a)). Qed.
Lemma lem3381682 {A : Type'} (_35448 : A) (a : A) : (_35448 = a) = (_35448 = a).
Proof. exact (eq_refl (_35448 = a)). Qed.
Lemma lem3381683 {A B : Type'} (s : A -> Prop) (f : A -> B) (_35448 : A) (a : A) : (term275 A B s f _35448 a) = (term33 A B s f _35448 a).
Proof. exact (MK_COMB (@lem3381681 A B s _35448 f a) (@lem3381682 A _35448 a)). Qed.
Lemma lem3381684 {A B : Type'} (s : A -> Prop) (f : A -> B) (_35448 : A) (a : A) : (term272 A B s _35448 f a) = (term33 A B s f _35448 a).
Proof. exact (TRANS (@lem3381666 A B s f _35448 a) (@lem3381683 A B s f _35448 a)). Qed.
Lemma lem3381686 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term150 A B x' s x f a) (h2 : x = (f a)) : term29 A B s x' f a.
Proof. exact (conj (@lem3381438 A B x' s x f a h1) (@lem3381579 A B x' s x f a h1 h2)). Qed.
Lemma lem3381688 {A B : Type'} (_35448 : A) (s : A -> Prop) (f : A -> B) (a : A) (h1 : term37 A B s f a) : term33 A B s f _35448 a.
Proof. exact (EQ_MP (@lem3381684 A B s f _35448 a) (@lem3381663 A B _35448 s f a h1)). Qed.
Lemma lem3381689 {A B : Type'} (_35448 : A) (s : A -> Prop) (f : A -> B) (a : A) (h1 : term37 A B s f a) : term33 A B s f _35448 a.
Proof. exact (@lem3381688 A B _35448 s f a h1). Qed.
Lemma lem3381690 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (a : A) (h1 : term37 A B s f a) : term33 A B s f x' a.
Proof. exact (@lem3381689 A B x' s f a h1). Qed.
Lemma lem3381693 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term37 A B s f a) (h2 : term150 A B x' s x f a) (h3 : x = (f a)) : x' = a.
Proof. exact (@lem3381690 A B x' s f a h1 (@lem3381686 A B x' s x f a h2 h3)). Qed.
Lemma lem3381694 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term37 A B s f a) (h2 : term150 A B x' s x f a) (h3 : x = (f a)) : term282 A x' a.
Proof. exact (fun h0 : term45 A x' a => @lem3381693 A B x' s x f a h1 h2 h3). Qed.
Lemma lem3381696 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3381697 {A : Type'} (x' : A) (a : A) : (term282 A x' a) = (x' = a).
Proof. exact (@lem3381696 (x' = a)). Qed.
Lemma lem3381698 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term37 A B s f a) (h2 : term150 A B x' s x f a) (h3 : x = (f a)) : x' = a.
Proof. exact (EQ_MP (@lem3381697 A x' a) (@lem3381694 A B x' s x f a h1 h2 h3)). Qed.
Lemma lem3381701 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3381703 {A : Type'} (x' : A) (a : A) : (term45 A x' a) = (term283 A x' a).
Proof. exact (@lem3381701 (x' = a)). Qed.
Lemma lem3381706 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term150 A B x' s x f a) : term283 A x' a.
Proof. exact (EQ_MP (@lem3381703 A x' a) (@lem3381278 A B x' s x f a h1)). Qed.
Lemma lem3381709 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term37 A B s f a) (h2 : term150 A B x' s x f a) (h3 : x = (f a)) : False.
Proof. exact (@lem3381706 A B x' s x f a h2 (@lem3381698 A B x' s x f a h1 h2 h3)). Qed.
Lemma lem3381710 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term37 A B s f a) (h2 : term150 A B x' s x f a) (h3 : x = (f a)) : term244.
Proof. exact (fun h0 : ~ False => @lem3381709 A B x' s x f a h1 h2 h3). Qed.
Lemma lem3381712 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3381713 : term244 = False.
Proof. exact (@lem3381712 False). Qed.
Lemma lem3381727 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3381728 {A : Type'} (_35491 : A) (_35492 : A) (h1 : _35491 = _35492) : _35491 = _35492.
Proof. exact (h1). Qed.
Lemma lem3381729 {A B : Type'} (f : A -> B) (_35491 : A) (_35492 : A) (h1 : _35491 = _35492) : (f _35491) = (f _35492).
Proof. exact (MK_COMB (@lem3381727 A B f) (@lem3381728 A _35491 _35492 h1)). Qed.
Lemma lem3381730 {A B : Type'} (_35491 : A) (f : A -> B) (_35492 : A) : term284 A B _35491 f _35492.
Proof. exact (fun h0 : _35491 = _35492 => @lem3381729 A B f _35491 _35492 h0). Qed.
Lemma lem3381732 (a : Prop) (b : Prop) : (a -> b) = (term285 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3381733 {A B : Type'} (_35491 : A) (f : A -> B) (_35492 : A) : (term284 A B _35491 f _35492) = (term286 A B _35491 f _35492).
Proof. exact (@lem3381732 (_35491 = _35492) ((f _35491) = (f _35492))). Qed.
Lemma lem3381734 {A B : Type'} (_35491 : A) (f : A -> B) (_35492 : A) : term286 A B _35491 f _35492.
Proof. exact (EQ_MP (@lem3381733 A B _35491 f _35492) (@lem3381730 A B _35491 f _35492)). Qed.
Lemma lem3381740 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3381741 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3381740 B x). Qed.
Lemma lem3381742 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem3381741 B (f x')). Qed.
Lemma lem3381743 {A B : Type'} (f : A -> B) (x' : A) : term233 A B f x'.
Proof. exact (fun h0 : term234 A B f x' => @lem3381742 A B f x'). Qed.
Lemma lem3381745 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3381746 {A B : Type'} (f : A -> B) (x' : A) : (term233 A B f x') = ((f x') = (f x')).
Proof. exact (@lem3381745 ((f x') = (f x'))). Qed.
Lemma lem3381747 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3381746 A B f x') (@lem3381743 A B f x')). Qed.
Lemma lem3381749 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : s x'.
Proof. exact (proj2 (@lem3380922 A B s x' x f a h1)). Qed.
Lemma lem3381750 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : term236 A s x'.
Proof. exact (fun h0 : term209 A s x' => @lem3381749 A B s x' x f a h1). Qed.
Lemma lem3381752 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3381753 {A : Type'} (s : A -> Prop) (x' : A) : (term236 A s x') = (s x').
Proof. exact (@lem3381752 (s x')). Qed.
Lemma lem3381754 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : s x'.
Proof. exact (EQ_MP (@lem3381753 A s x') (@lem3381750 A B s x' x f a h1)). Qed.
Lemma lem3381760 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3381761 {A B : Type'} (s : A -> Prop) (x' : A) (f : A -> B) (_35450 : A) (a : A) : (term225 A B x' f s _35450 a) = (term287 A B s x' f _35450 a).
Proof. exact (@lem3381760 (term209 A s _35450) (term210 A B x' f _35450) (_35450 = a)). Qed.
Lemma lem3381775 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3381776 {A B : Type'} (a : A) (x' : A) (f : A -> B) (_35450 : A) : (term288 A B x' f _35450 a) = (term289 A B a x' f _35450).
Proof. exact (@lem3381775 (_35450 = a) (term210 A B x' f _35450)). Qed.
Lemma lem3381786 {A : Type'} (s : A -> Prop) (_35450 : A) : (term95 A s _35450) = (term95 A s _35450).
Proof. exact (eq_refl (term95 A s _35450)). Qed.
Lemma lem3381787 {A B : Type'} (s : A -> Prop) (a : A) (x' : A) (f : A -> B) (_35450 : A) : (term287 A B s x' f _35450 a) = (term290 A B s a x' f _35450).
Proof. exact (MK_COMB (@lem3381786 A s _35450) (@lem3381776 A B a x' f _35450)). Qed.
Lemma lem3381791 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3381792 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (_35450 : A) : (term290 A B s a x' f _35450) = (term291 A B a s x' f _35450).
Proof. exact (@lem3381791 (_35450 = a) (term209 A s _35450) (term210 A B x' f _35450)). Qed.
Lemma lem3381812 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (_35450 : A) : (term287 A B s x' f _35450 a) = (term291 A B a s x' f _35450).
Proof. exact (TRANS (@lem3381787 A B s a x' f _35450) (@lem3381792 A B a s x' f _35450)). Qed.
Lemma lem3381813 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (_35450 : A) : (term225 A B x' f s _35450 a) = (term291 A B a s x' f _35450).
Proof. exact (TRANS (@lem3381761 A B s x' f _35450 a) (@lem3381812 A B a s x' f _35450)). Qed.
Lemma lem3381814 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3381815 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (_35450 : A) : (term292 A B x' f s _35450 a) = (term293 A B a s x' f _35450).
Proof. exact (MK_COMB (@lem3381814) (@lem3381813 A B a s x' f _35450)). Qed.
Lemma lem3381831 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3381832 {A B : Type'} (s : A -> Prop) (x' : A) (f : A -> B) (_35450 : A) : (term214 A B x' f s _35450) = (term294 A B s x' f _35450).
Proof. exact (@lem3381831 (term209 A s _35450) (term210 A B x' f _35450)). Qed.
Lemma lem3381840 {A : Type'} (_35450 : A) (a : A) : (term295 A _35450 a) = (term295 A _35450 a).
Proof. exact (eq_refl (term295 A _35450 a)). Qed.
Lemma lem3381841 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (_35450 : A) : (term296 A B a x' f s _35450) = (term291 A B a s x' f _35450).
Proof. exact (MK_COMB (@lem3381840 A _35450 a) (@lem3381832 A B s x' f _35450)). Qed.
Lemma lem3381852 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (_35450 : A) : ((term225 A B x' f s _35450 a) = (term296 A B a x' f s _35450)) = ((term291 A B a s x' f _35450) = (term291 A B a s x' f _35450)).
Proof. exact (MK_COMB (@lem3381815 A B a s x' f _35450) (@lem3381841 A B a s x' f _35450)). Qed.
Lemma lem3381854 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3381855 (x : Prop) : (x = x) = True.
Proof. exact (@lem3381854 Prop x). Qed.
Lemma lem3381856 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (_35450 : A) : ((term291 A B a s x' f _35450) = (term291 A B a s x' f _35450)) = True.
Proof. exact (@lem3381855 (term291 A B a s x' f _35450)). Qed.
Lemma lem3381857 {A B : Type'} (a : A) (x' : A) (f : A -> B) (s : A -> Prop) (_35450 : A) : ((term225 A B x' f s _35450 a) = (term296 A B a x' f s _35450)) = True.
Proof. exact (TRANS (@lem3381852 A B a s x' f _35450) (@lem3381856 A B a s x' f _35450)). Qed.
Lemma lem3381858 {A B : Type'} (a : A) (x' : A) (f : A -> B) (s : A -> Prop) (_35450 : A) : True = ((term225 A B x' f s _35450 a) = (term296 A B a x' f s _35450)).
Proof. exact (SYM (@lem3381857 A B a x' f s _35450)). Qed.
Lemma lem3381859 {A B : Type'} (a : A) (x' : A) (f : A -> B) (s : A -> Prop) (_35450 : A) : (term225 A B x' f s _35450 a) = (term296 A B a x' f s _35450).
Proof. exact (EQ_MP (@lem3381858 A B a x' f s _35450) (@lem0)). Qed.
Lemma lem3381860 {A B : Type'} (_35450 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : term296 A B a x' f s _35450.
Proof. exact (EQ_MP (@lem3381859 A B a x' f s _35450) (@lem3381319 A B _35450 s x' x f a h1)). Qed.
Lemma lem3381862 (b : Prop) (a : Prop) : (a \/ b) = (term254 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3381863 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35450 : A) (a : A) : (term296 A B a x' f s _35450) = (term297 A B x' f s _35450 a).
Proof. exact (@lem3381862 (term214 A B x' f s _35450) (_35450 = a)). Qed.
Lemma lem3381865 (a : Prop) (b : Prop) : (term257 a b) = (term258 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3381866 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35450 : A) : (term298 A B x' f s _35450) = (term299 A B x' f s _35450).
Proof. exact (@lem3381865 (term210 A B x' f _35450) (term209 A s _35450)). Qed.
Lemma lem3381868 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3381869 {A B : Type'} (x' : A) (f : A -> B) (_35450 : A) : (term280 A B x' f _35450) = ((f x') = (f _35450)).
Proof. exact (@lem3381868 ((f x') = (f _35450))). Qed.
Lemma lem3381870 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3381871 {A B : Type'} (x' : A) (f : A -> B) (_35450 : A) : (term300 A B x' f _35450) = (term301 A B x' f _35450).
Proof. exact (MK_COMB (@lem3381870) (@lem3381869 A B x' f _35450)). Qed.
Lemma lem3381873 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3381874 {A : Type'} (s : A -> Prop) (_35450 : A) : (term278 A s _35450) = (s _35450).
Proof. exact (@lem3381873 (s _35450)). Qed.
Lemma lem3381875 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35450 : A) : (term299 A B x' f s _35450) = (term241 A B x' f s _35450).
Proof. exact (MK_COMB (@lem3381871 A B x' f _35450) (@lem3381874 A s _35450)). Qed.
Lemma lem3381876 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35450 : A) : (term298 A B x' f s _35450) = (term241 A B x' f s _35450).
Proof. exact (TRANS (@lem3381866 A B x' f s _35450) (@lem3381875 A B x' f s _35450)). Qed.
Lemma lem3381877 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3381878 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35450 : A) : (term302 A B x' f s _35450) = (term303 A B x' f s _35450).
Proof. exact (MK_COMB (@lem3381877) (@lem3381876 A B x' f s _35450)). Qed.
Lemma lem3381879 {A : Type'} (_35450 : A) (a : A) : (_35450 = a) = (_35450 = a).
Proof. exact (eq_refl (_35450 = a)). Qed.
Lemma lem3381880 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35450 : A) (a : A) : (term297 A B x' f s _35450 a) = (term304 A B x' f s _35450 a).
Proof. exact (MK_COMB (@lem3381878 A B x' f s _35450) (@lem3381879 A _35450 a)). Qed.
Lemma lem3381881 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35450 : A) (a : A) : (term296 A B a x' f s _35450) = (term304 A B x' f s _35450 a).
Proof. exact (TRANS (@lem3381863 A B x' f s _35450 a) (@lem3381880 A B x' f s _35450 a)). Qed.
Lemma lem3381883 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : term242 A B f s x'.
Proof. exact (conj (@lem3381747 A B f x') (@lem3381754 A B s x' x f a h1)). Qed.
Lemma lem3381885 {A B : Type'} (_35450 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : term304 A B x' f s _35450 a.
Proof. exact (EQ_MP (@lem3381881 A B x' f s _35450 a) (@lem3381860 A B _35450 s x' x f a h1)). Qed.
Lemma lem3381886 {A B : Type'} (_35450 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : term304 A B x' f s _35450 a.
Proof. exact (@lem3381885 A B _35450 s x' x f a h1). Qed.
Lemma lem3381887 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : term305 A B f s x' a.
Proof. exact (@lem3381886 A B x' s x' x f a h1). Qed.
Lemma lem3381890 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : x' = a.
Proof. exact (@lem3381887 A B s x' x f a h1 (@lem3381883 A B s x' x f a h1)). Qed.
Lemma lem3381891 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : term282 A x' a.
Proof. exact (fun h0 : term45 A x' a => @lem3381890 A B s x' x f a h1). Qed.
Lemma lem3381893 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3381894 {A : Type'} (x' : A) (a : A) : (term282 A x' a) = (x' = a).
Proof. exact (@lem3381893 (x' = a)). Qed.
Lemma lem3381895 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : x' = a.
Proof. exact (EQ_MP (@lem3381894 A x' a) (@lem3381891 A B s x' x f a h1)). Qed.
Lemma lem3381901 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3381902 {A B : Type'} (f : A -> B) (_35491 : A) (_35492 : A) : (term286 A B _35491 f _35492) = (term306 A B f _35491 _35492).
Proof. exact (@lem3381901 ((f _35491) = (f _35492)) (term45 A _35491 _35492)). Qed.
Lemma lem3381912 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3381913 {A B : Type'} (f : A -> B) (_35491 : A) (_35492 : A) : (term307 A B _35491 f _35492) = (term308 A B f _35491 _35492).
Proof. exact (MK_COMB (@lem3381912) (@lem3381902 A B f _35491 _35492)). Qed.
Lemma lem3381923 {A B : Type'} (f : A -> B) (_35491 : A) (_35492 : A) : (term306 A B f _35491 _35492) = (term306 A B f _35491 _35492).
Proof. exact (eq_refl (term306 A B f _35491 _35492)). Qed.
Lemma lem3381924 {A B : Type'} (f : A -> B) (_35491 : A) (_35492 : A) : ((term286 A B _35491 f _35492) = (term306 A B f _35491 _35492)) = ((term306 A B f _35491 _35492) = (term306 A B f _35491 _35492)).
Proof. exact (MK_COMB (@lem3381913 A B f _35491 _35492) (@lem3381923 A B f _35491 _35492)). Qed.
Lemma lem3381926 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3381927 (x : Prop) : (x = x) = True.
Proof. exact (@lem3381926 Prop x). Qed.
Lemma lem3381928 {A B : Type'} (f : A -> B) (_35491 : A) (_35492 : A) : ((term306 A B f _35491 _35492) = (term306 A B f _35491 _35492)) = True.
Proof. exact (@lem3381927 (term306 A B f _35491 _35492)). Qed.
Lemma lem3381929 {A B : Type'} (f : A -> B) (_35491 : A) (_35492 : A) : ((term286 A B _35491 f _35492) = (term306 A B f _35491 _35492)) = True.
Proof. exact (TRANS (@lem3381924 A B f _35491 _35492) (@lem3381928 A B f _35491 _35492)). Qed.
Lemma lem3381930 {A B : Type'} (f : A -> B) (_35491 : A) (_35492 : A) : True = ((term286 A B _35491 f _35492) = (term306 A B f _35491 _35492)).
Proof. exact (SYM (@lem3381929 A B f _35491 _35492)). Qed.
Lemma lem3381931 {A B : Type'} (f : A -> B) (_35491 : A) (_35492 : A) : (term286 A B _35491 f _35492) = (term306 A B f _35491 _35492).
Proof. exact (EQ_MP (@lem3381930 A B f _35491 _35492) (@lem0)). Qed.
Lemma lem3381932 {A B : Type'} (f : A -> B) (_35491 : A) (_35492 : A) : term306 A B f _35491 _35492.
Proof. exact (EQ_MP (@lem3381931 A B f _35491 _35492) (@lem3381734 A B _35491 f _35492)). Qed.
Lemma lem3381934 (b : Prop) (a : Prop) : (a \/ b) = (term254 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3381935 {A B : Type'} (_35491 : A) (f : A -> B) (_35492 : A) : (term306 A B f _35491 _35492) = (term309 A B _35491 f _35492).
Proof. exact (@lem3381934 (term45 A _35491 _35492) ((f _35491) = (f _35492))). Qed.
Lemma lem3381937 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3381938 {A : Type'} (_35491 : A) (_35492 : A) : (term94 A _35491 _35492) = (_35491 = _35492).
Proof. exact (@lem3381937 (_35491 = _35492)). Qed.
Lemma lem3381939 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3381940 {A : Type'} (_35491 : A) (_35492 : A) : (term310 A _35491 _35492) = (term311 A _35491 _35492).
Proof. exact (MK_COMB (@lem3381939) (@lem3381938 A _35491 _35492)). Qed.
Lemma lem3381941 {A B : Type'} (_35491 : A) (f : A -> B) (_35492 : A) : ((f _35491) = (f _35492)) = ((f _35491) = (f _35492)).
Proof. exact (eq_refl ((f _35491) = (f _35492))). Qed.
Lemma lem3381942 {A B : Type'} (_35491 : A) (f : A -> B) (_35492 : A) : (term309 A B _35491 f _35492) = (term284 A B _35491 f _35492).
Proof. exact (MK_COMB (@lem3381940 A _35491 _35492) (@lem3381941 A B _35491 f _35492)). Qed.
Lemma lem3381943 {A B : Type'} (_35491 : A) (f : A -> B) (_35492 : A) : (term306 A B f _35491 _35492) = (term284 A B _35491 f _35492).
Proof. exact (TRANS (@lem3381935 A B _35491 f _35492) (@lem3381942 A B _35491 f _35492)). Qed.
Lemma lem3381946 {A B : Type'} (_35491 : A) (f : A -> B) (_35492 : A) : term284 A B _35491 f _35492.
Proof. exact (EQ_MP (@lem3381943 A B _35491 f _35492) (@lem3381932 A B f _35491 _35492)). Qed.
Lemma lem3381947 {A B : Type'} (_35491 : A) (f : A -> B) (_35492 : A) : term284 A B _35491 f _35492.
Proof. exact (@lem3381946 A B _35491 f _35492). Qed.
Lemma lem3381948 {A B : Type'} (x' : A) (f : A -> B) (a : A) : term284 A B x' f a.
Proof. exact (@lem3381947 A B x' f a). Qed.
Lemma lem3381951 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : (f x') = (f a).
Proof. exact (@lem3381948 A B x' f a (@lem3381895 A B s x' x f a h1)). Qed.
Lemma lem3381952 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : term246 A B x' f a.
Proof. exact (fun h0 : term210 A B x' f a => @lem3381951 A B s x' x f a h1). Qed.
Lemma lem3381954 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3381955 {A B : Type'} (x' : A) (f : A -> B) (a : A) : (term246 A B x' f a) = ((f x') = (f a)).
Proof. exact (@lem3381954 ((f x') = (f a))). Qed.
Lemma lem3381956 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : (f x') = (f a).
Proof. exact (EQ_MP (@lem3381955 A B x' f a) (@lem3381952 A B s x' x f a h1)). Qed.
Lemma lem3381959 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3381961 {A B : Type'} (x' : A) (f : A -> B) (a : A) : (term210 A B x' f a) = (term312 A B x' f a).
Proof. exact (@lem3381959 ((f x') = (f a))). Qed.
Lemma lem3381964 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : term312 A B x' f a.
Proof. exact (EQ_MP (@lem3381961 A B x' f a) (@lem3381332 A B s x' x f a h1)). Qed.
Lemma lem3381967 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : False.
Proof. exact (@lem3381964 A B s x' x f a h1 (@lem3381956 A B s x' x f a h1)). Qed.
Lemma lem3381968 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : term244.
Proof. exact (fun h0 : ~ False => @lem3381967 A B s x' x f a h1). Qed.
Lemma lem3381970 (p : Prop) : (term235 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3381971 : term244 = False.
Proof. exact (@lem3381970 False). Qed.
Lemma lem3381973 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term180 A B s x' x f a) : False.
Proof. exact (EQ_MP (@lem3381971) (@lem3381968 A B s x' x f a h1)). Qed.
Lemma lem3381974 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term37 A B s f a) (h2 : term150 A B x' s x f a) (h3 : x = (f a)) : False.
Proof. exact (EQ_MP (@lem3381713) (@lem3381710 A B x' s x f a h1 h2 h3)). Qed.
Lemma lem3381975 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term120 A B x f s) (h2 : term150 A B x' s x f a) : False.
Proof. exact (EQ_MP (@lem3381406) (@lem3381403 A B x' s x f a h1 h2)). Qed.
Lemma lem3381976 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term37 A B s f a) (h2 : term150 A B x' s x f a) (h3 : x = (f a)) : (x = (f a)) = False.
Proof. exact (prop_ext (fun h4 : x = (f a) => @lem3381974 A B x' s x f a h1 h2 h3) (fun h4 : False => @lem3381112 A B x f a h3)). Qed.
Lemma lem3381977 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term37 A B s f a) (h2 : term150 A B x' s x f a) (h3 : x = (f a)) : False.
Proof. exact (EQ_MP (@lem3381976 A B x' s x f a h1 h2 h3) (@lem3381112 A B x f a h3)). Qed.
Lemma lem3381978 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term37 A B s f a) (h2 : term150 A B x' s x f a) (h3 : x = (f a)) : (x = (f a)) = False.
Proof. exact (prop_ext (fun h4 : x = (f a) => @lem3381977 A B x' s x f a h1 h2 h3) (fun h4 : False => @lem3381003 A B x f a h3)). Qed.
Lemma lem3381979 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term37 A B s f a) (h2 : term150 A B x' s x f a) (h3 : x = (f a)) : False.
Proof. exact (EQ_MP (@lem3381978 A B x' s x f a h1 h2 h3) (@lem3381003 A B x f a h3)). Qed.
Lemma lem3381980 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term37 A B s f a) (h2 : term150 A B x' s x f a) (h3 : x = (f a)) : (x = (f a)) = False.
Proof. exact (prop_ext (fun h4 : x = (f a) => @lem3381979 A B x' s x f a h1 h2 h3) (fun h4 : False => @lem3381003 A B x f a h3)). Qed.
Lemma lem3381981 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term37 A B s f a) (h2 : term150 A B x' s x f a) (h3 : x = (f a)) : False.
Proof. exact (EQ_MP (@lem3381980 A B x' s x f a h1 h2 h3) (@lem3381003 A B x f a h3)). Qed.
Lemma lem3381982 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term120 A B x f s) (h2 : term150 A B x' s x f a) : (term120 A B x f s) = False.
Proof. exact (prop_ext (fun h3 : term120 A B x f s => @lem3381975 A B x' s x f a h1 h2) (fun h3 : False => @lem3380968 A B x f s h1)). Qed.
Lemma lem3381983 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term120 A B x f s) (h2 : term150 A B x' s x f a) : False.
Proof. exact (EQ_MP (@lem3381982 A B x' s x f a h1 h2) (@lem3380968 A B x f s h1)). Qed.
Lemma lem3381984 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term37 A B s f a) (h2 : term150 A B x' s x f a) : False.
Proof. exact (or_elim (@lem3380911 A B x' s x f a h2) (fun h0 : term120 A B x f s => @lem3381983 A B x' s x f a h0 h2) (fun h0 : x = (f a) => @lem3381981 A B x' s x f a h1 h2 h0)). Qed.
Lemma lem3381985 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term37 A B s f a) (h2 : term201 A B s x' x f a) : False.
Proof. exact (or_elim (@lem3380908 A B s x' x f a h2) (fun h0 : term150 A B x' s x f a => @lem3381984 A B x' s x f a h1 h0) (fun h0 : term180 A B s x' x f a => @lem3381973 A B s x' x f a h0)). Qed.
Lemma lem3381986 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term37 A B s f a) (h2 : term201 A B s x' x f a) : (term201 A B s x' x f a) = False.
Proof. exact (prop_ext (fun h3 : term201 A B s x' x f a => @lem3381985 A B s x' x f a h1 h2) (fun h3 : False => @lem3380908 A B s x' x f a h2)). Qed.
Lemma lem3381987 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (a : A) (h1 : term37 A B s f a) (h2 : term201 A B s x' x f a) : False.
Proof. exact (EQ_MP (@lem3381986 A B s x' x f a h1 h2) (@lem3380908 A B s x' x f a h2)). Qed.
Lemma lem3381988 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term37 A B s f a) (h2 : term85 A B s x f a) : False.
Proof. exact (ex_elim (@lem3380760 A B s x f a h2) (fun x' : A => fun h0 : term203 A B s x f a x' => @lem3381987 A B s x' x f a h1 h0)). Qed.
Lemma lem3381989 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term37 A B s f a) (h2 : term85 A B s x f a) : (term85 A B s x f a) = False.
Proof. exact (prop_ext (fun h3 : term85 A B s x f a => @lem3381988 A B s x f a h1 h2) (fun h3 : False => @lem3380324 A B s x f a h2)). Qed.
Lemma lem3381990 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (a : A) (h1 : term37 A B s f a) (h2 : term85 A B s x f a) : False.
Proof. exact (EQ_MP (@lem3381989 A B s x f a h1 h2) (@lem3380324 A B s x f a h2)). Qed.
Lemma lem3381991 {A B : Type'} (x : B) (s : A -> Prop) (f : A -> B) (a : A) (h1 : term37 A B s f a) : term84 A B s x f a.
Proof. exact (fun h0 : term85 A B s x f a => @lem3381990 A B s x f a h1 h0). Qed.
Lemma lem3381992 {A B : Type'} (x : B) (s : A -> Prop) (f : A -> B) (a : A) (h1 : term37 A B s f a) : (term52 A B x f s a) = (term65 A B s x f a).
Proof. exact (EQ_MP (@lem3380323 A B s x f a) (@lem3381991 A B x s f a h1)). Qed.
Lemma lem3381997 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) (h1 : term37 A B s f a) : term68 A B s f a.
Proof. exact (fun x : B => @lem3381992 A B x s f a h1). Qed.
Lemma lem3381998 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : term69 A B s f a.
Proof. exact (fun h0 : term37 A B s f a => @lem3381997 A B s f a h0). Qed.
Lemma lem3382003 {A B : Type'} (s : A -> Prop) (f : A -> B) : term71 A B s f.
Proof. exact (fun a : A => @lem3381998 A B s f a). Qed.
Lemma lem3382008 {A B : Type'} (f : A -> B) : term73 A B f.
Proof. exact (fun s : A -> Prop => @lem3382003 A B s f). Qed.
Lemma lem3382013 {A B : Type'} : term75 A B.
Proof. exact (fun f : A -> B => @lem3382008 A B f). Qed.
Lemma lem3382014 {A B : Type'} : term77 A B.
Proof. exact (EQ_MP (@lem3380318 A B) (@lem3382013 A B)). Qed.
Lemma lem3382016 {A B : Type'} : term77 A B.
Proof. exact (@lem3380075 A B (@lem3382014 A B)). Qed.
Lemma lem3382017 {A B : Type'} (h1 : term78 A B) : False.
Proof. exact (@lem3382016 A B (@lem3380059 A B h1)). Qed.
Lemma lem3382018 {A B : Type'} (h1 : term78 A B) : (term78 A B) = False.
Proof. exact (prop_ext (fun h2 : term78 A B => @lem3382017 A B h1) (fun h2 : False => @lem3380059 A B h1)). Qed.
Lemma lem3382019 {A B : Type'} (h1 : term78 A B) : False.
Proof. exact (EQ_MP (@lem3382018 A B h1) (@lem3380059 A B h1)). Qed.
Lemma lem3382020 {A B : Type'} : term77 A B.
Proof. exact (fun h0 : term78 A B => @lem3382019 A B h0). Qed.
Lemma lem3382021 {A B : Type'} : term75 A B.
Proof. exact (EQ_MP (@lem3380058 A B) (@lem3382020 A B)). Qed.
Lemma lem3382022 {A B : Type'} : term25 A B.
Proof. exact (EQ_MP (@lem3380054 A B) (@lem3382021 A B)). Qed.
Lemma lem3382023 {A B : Type'} : term24 A B.
Proof. exact (EQ_MP (@lem3379874 A B) (@lem3382022 A B)). Qed.
