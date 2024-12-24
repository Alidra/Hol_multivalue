Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INSERT_DELETE_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
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
Lemma lem3318908 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3318909 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3318908 A s t). Qed.
Lemma lem3318910 {A : Type'} (x : A) (s : A -> Prop) : ((term1 A s x) = s) = (term2 A x s).
Proof. exact (@lem3318909 A (term1 A s x) s). Qed.
Lemma lem3318919 {A : Type'} (x : A) (s : A -> Prop) : (term3 A x s) = (term3 A x s).
Proof. exact (eq_refl (term3 A x s)). Qed.
Lemma lem3318920 {A : Type'} (x : A) (s : A -> Prop) : (term4 A x s) = (term5 A x s).
Proof. exact (MK_COMB (@lem3318919 A x s) (@lem3318910 A x s)). Qed.
Lemma lem3318923 {A : Type'} (x : A) : (term6 A x) = (term7 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3318920 A x s)). Qed.
Lemma lem3318924 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3318925 {A : Type'} (x : A) : (term8 A x) = (term9 A x).
Proof. exact (MK_COMB (@lem3318924 A) (@lem3318923 A x)). Qed.
Lemma lem3318930 {A : Type'} : (term10 A) = (term11 A).
Proof. exact (fun_ext (fun x : A => @lem3318925 A x)). Qed.
Lemma lem3318931 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3318932 {A : Type'} : (term12 A) = (term13 A).
Proof. exact (MK_COMB (@lem3318931 A) (@lem3318930 A)). Qed.
Lemma lem3318937 {A : Type'} : (term13 A) = (term12 A).
Proof. exact (SYM (@lem3318932 A)). Qed.
Lemma lem3318949 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3318950 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3318949 A P x). Qed.
Lemma lem3318951 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3318950 A s x). Qed.
Lemma lem3318952 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3318953 {A : Type'} (s : A -> Prop) (x : A) : (term3 A x s) = (term14 A s x).
Proof. exact (MK_COMB (@lem3318952) (@lem3318951 A s x)). Qed.
Lemma lem3318961 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term15 A x y s) = (term16 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3318962 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term15 A x y s) = (term16 A y x s).
Proof. exact (@lem3318961 A y x s). Qed.
Lemma lem3318963 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : (term17 A x' s x) = (term18 A x' s x).
Proof. exact (@lem3318962 A x x' (@DELETE A s x)). Qed.
Lemma lem3318969 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term19 A x s y) = (term20 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3318970 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term19 A x s y) = (term20 A s x y).
Proof. exact (@lem3318969 A s x y). Qed.
Lemma lem3318971 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term19 A x' s x) = (term20 A s x' x).
Proof. exact (@lem3318970 A s x' x). Qed.
Lemma lem3318975 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3318976 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3318975 A P x). Qed.
Lemma lem3318977 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3318976 A s x'). Qed.
Lemma lem3318978 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3318979 {A : Type'} (s : A -> Prop) (x' : A) : (term21 A x' s) = (term22 A s x').
Proof. exact (MK_COMB (@lem3318978) (@lem3318977 A s x')). Qed.
Lemma lem3318982 {A : Type'} (x' : A) (x : A) : (term23 A x' x) = (term23 A x' x).
Proof. exact (eq_refl (term23 A x' x)). Qed.
Lemma lem3318983 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term20 A s x' x) = (term24 A s x' x).
Proof. exact (MK_COMB (@lem3318979 A s x') (@lem3318982 A x' x)). Qed.
Lemma lem3318986 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term19 A x' s x) = (term24 A s x' x).
Proof. exact (TRANS (@lem3318971 A s x' x) (@lem3318983 A s x' x)). Qed.
Lemma lem3318987 {A : Type'} (x' : A) (x : A) : (term25 A x' x) = (term25 A x' x).
Proof. exact (eq_refl (term25 A x' x)). Qed.
Lemma lem3318988 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term18 A x' s x) = (term26 A s x' x).
Proof. exact (MK_COMB (@lem3318987 A x' x) (@lem3318986 A s x' x)). Qed.
Lemma lem3318991 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term17 A x' s x) = (term26 A s x' x).
Proof. exact (TRANS (@lem3318963 A x' s x) (@lem3318988 A s x' x)). Qed.
Lemma lem3318992 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3318993 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term27 A x' s x) = (term28 A s x' x).
Proof. exact (MK_COMB (@lem3318992) (@lem3318991 A s x' x)). Qed.
Lemma lem3318995 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3318996 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3318995 A P x). Qed.
Lemma lem3318997 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3318996 A s x'). Qed.
Lemma lem3318998 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term17 A x' s x) = (@IN A x' s)) = ((term26 A s x' x) = (s x')).
Proof. exact (MK_COMB (@lem3318993 A s x' x) (@lem3318997 A s x')). Qed.
Lemma lem3319001 {A : Type'} (x : A) (s : A -> Prop) : (term29 A x s) = (term30 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3318998 A x s x')). Qed.
Lemma lem3319002 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3319003 {A : Type'} (x : A) (s : A -> Prop) : (term2 A x s) = (term31 A x s).
Proof. exact (MK_COMB (@lem3319002 A) (@lem3319001 A x s)). Qed.
Lemma lem3319008 {A : Type'} (x : A) (s : A -> Prop) : (term5 A x s) = (term32 A x s).
Proof. exact (MK_COMB (@lem3318953 A s x) (@lem3319003 A x s)). Qed.
Lemma lem3319011 {A : Type'} (x : A) : (term7 A x) = (term33 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3319008 A x s)). Qed.
Lemma lem3319012 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3319013 {A : Type'} (x : A) : (term9 A x) = (term34 A x).
Proof. exact (MK_COMB (@lem3319012 A) (@lem3319011 A x)). Qed.
Lemma lem3319018 {A : Type'} : (term11 A) = (term35 A).
Proof. exact (fun_ext (fun x : A => @lem3319013 A x)). Qed.
Lemma lem3319019 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3319020 {A : Type'} : (term13 A) = (term36 A).
Proof. exact (MK_COMB (@lem3319019 A) (@lem3319018 A)). Qed.
Lemma lem3319025 {A : Type'} : (term36 A) = (term13 A).
Proof. exact (SYM (@lem3319020 A)). Qed.
Lemma lem3319027 (p : Prop) : p = (term37 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3319028 {A : Type'} : (term36 A) = (term38 A).
Proof. exact (@lem3319027 (term36 A)). Qed.
Lemma lem3319029 {A : Type'} : (term38 A) = (term36 A).
Proof. exact (SYM (@lem3319028 A)). Qed.
Lemma lem3319030 {A : Type'} (h1 : term39 A) : term39 A.
Proof. exact (h1). Qed.
Lemma lem3319033 {A : Type'} (h1 : term38 A) : term38 A.
Proof. exact (h1). Qed.
Lemma lem3319034 {A : Type'} : term40 A.
Proof. exact (fun h0 : term38 A => @lem3319033 A h0). Qed.
Lemma lem3319035 {A : Type'} (h1 : term40 A) : term40 A.
Proof. exact (h1). Qed.
Lemma lem3319036 {A : Type'} (h1 : term38 A) : term38 A.
Proof. exact (h1). Qed.
Lemma lem3319037 {A : Type'} (h1 : term38 A) (h2 : term40 A) : term38 A.
Proof. exact (@lem3319035 A h2 (@lem3319036 A h1)). Qed.
Lemma lem3319038 {A : Type'} (h1 : term38 A) : term41 A.
Proof. exact (fun h0 : term40 A => @lem3319037 A h1 h0). Qed.
Lemma lem3319039 {A : Type'} (h1 : term40 A) : term40 A.
Proof. exact (h1). Qed.
Lemma lem3319040 {A : Type'} (h1 : term38 A) (h2 : term40 A) : term38 A.
Proof. exact (@lem3319038 A h1 (@lem3319039 A h2)). Qed.
Lemma lem3319041 {A : Type'} (h1 : term40 A) : term40 A.
Proof. exact (fun h0 : term38 A => @lem3319040 A h0 h1). Qed.
Lemma lem3319042 {A : Type'} : term42 A.
Proof. exact (fun h0 : term40 A => @lem3319041 A h0). Qed.
Lemma lem3319045 {A : Type'} : term40 A.
Proof. exact (@lem3319042 A (@lem3319034 A)). Qed.
Lemma lem3319046 {A : Type'} : term40 A.
Proof. exact (@lem3319045 A). Qed.
Lemma lem3319048 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3319049 {A : Type'} : (term38 A) = (term43 A).
Proof. exact (@lem3319048 (term39 A)). Qed.
Lemma lem3319051 (t : Prop) : (term44 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3319052 {A : Type'} : (term43 A) = (term36 A).
Proof. exact (@lem3319051 (term36 A)). Qed.
Lemma lem3319075 {A : Type'} : (term38 A) = (term36 A).
Proof. exact (TRANS (@lem3319049 A) (@lem3319052 A)). Qed.
Lemma lem3319090 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term26 A s x' x) = (s x')) = ((term26 A s x' x) = (s x')).
Proof. exact (eq_refl ((term26 A s x' x) = (s x'))). Qed.
Lemma lem3319091 {A : Type'} (x : A) (s : A -> Prop) : (term30 A x s) = (term30 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3319090 A x s x')). Qed.
Lemma lem3319092 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3319093 {A : Type'} (x : A) (s : A -> Prop) : (term31 A x s) = (term31 A x s).
Proof. exact (MK_COMB (@lem3319092 A) (@lem3319091 A x s)). Qed.
Lemma lem3319096 {A : Type'} (s : A -> Prop) (x : A) : (term14 A s x) = (term14 A s x).
Proof. exact (eq_refl (term14 A s x)). Qed.
Lemma lem3319097 {A : Type'} (x : A) (s : A -> Prop) : (term32 A x s) = (term32 A x s).
Proof. exact (MK_COMB (@lem3319096 A s x) (@lem3319093 A x s)). Qed.
Lemma lem3319098 {A : Type'} (x : A) : (term33 A x) = (term33 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3319097 A x s)). Qed.
Lemma lem3319099 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3319100 {A : Type'} (x : A) : (term34 A x) = (term34 A x).
Proof. exact (MK_COMB (@lem3319099 A) (@lem3319098 A x)). Qed.
Lemma lem3319101 {A : Type'} : (term35 A) = (term35 A).
Proof. exact (fun_ext (fun x : A => @lem3319100 A x)). Qed.
Lemma lem3319102 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3319103 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (MK_COMB (@lem3319102 A) (@lem3319101 A)). Qed.
Lemma lem3319130 {A : Type'} : (term38 A) = (term36 A).
Proof. exact (TRANS (@lem3319075 A) (@lem3319103 A)). Qed.
Lemma lem3319131 {A : Type'} : (term36 A) = (term38 A).
Proof. exact (SYM (@lem3319130 A)). Qed.
Lemma lem3319134 (p : Prop) : p = (term37 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3319135 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term26 A s x' x) = (s x')) = (term45 A x s x').
Proof. exact (@lem3319134 ((term26 A s x' x) = (s x'))). Qed.
Lemma lem3319136 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term45 A x s x') = ((term26 A s x' x) = (s x')).
Proof. exact (SYM (@lem3319135 A x s x')). Qed.
Lemma lem3319137 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term46 A x s x') : term46 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3319143 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3319151 {A : Type'} (x' : A) (x : A) : (term47 A x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3319153 {A : Type'} (s : A -> Prop) (x' : A) : (term48 A s x') = (term48 A s x').
Proof. exact (eq_refl (term48 A s x')). Qed.
Lemma lem3319154 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term49 A s x' x) = (term50 A s x' x).
Proof. exact (MK_COMB (@lem3319153 A s x') (@lem3319151 A x' x)). Qed.
Lemma lem3319155 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term51 A s x' x) = (term49 A s x' x).
Proof. exact (@lem17045 (s x') (term23 A x' x)). Qed.
Lemma lem3319156 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term51 A s x' x) = (term50 A s x' x).
Proof. exact (TRANS (@lem3319155 A s x' x) (@lem3319154 A s x' x)). Qed.
Lemma lem3319161 {A : Type'} (x' : A) (x : A) : (term52 A x' x) = (term52 A x' x).
Proof. exact (eq_refl (term52 A x' x)). Qed.
Lemma lem3319162 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term53 A s x' x) = (term54 A s x' x).
Proof. exact (MK_COMB (@lem3319161 A x' x) (@lem3319156 A s x' x)). Qed.
Lemma lem3319163 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term55 A s x' x) = (term53 A s x' x).
Proof. exact (@lem17160 (x' = x) (term24 A s x' x)). Qed.
Lemma lem3319164 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term55 A s x' x) = (term54 A s x' x).
Proof. exact (TRANS (@lem3319163 A s x' x) (@lem3319162 A s x' x)). Qed.
Lemma lem3319169 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (s x').
Proof. exact (eq_refl (s x')). Qed.
Lemma lem3319170 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3319171 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term56 A s x' x) = (term57 A s x' x).
Proof. exact (MK_COMB (@lem3319170) (@lem3319164 A s x' x)). Qed.
Lemma lem3319172 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term58 A x s x') = (term59 A x s x').
Proof. exact (MK_COMB (@lem3319171 A s x' x) (@lem3319169 A s x')). Qed.
Lemma lem3319177 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term60 A x s x') = (term60 A x s x').
Proof. exact (eq_refl (term60 A x s x')). Qed.
Lemma lem3319178 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term61 A x s x') = (term62 A x s x').
Proof. exact (MK_COMB (@lem3319177 A x s x') (@lem3319172 A x s x')). Qed.
Lemma lem3319179 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term46 A x s x') = (term61 A x s x').
Proof. exact (@lem17646 (term26 A s x' x) (s x')). Qed.
Lemma lem3319184 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term46 A x s x') = (term62 A x s x').
Proof. exact (TRANS (@lem3319179 A x s x') (@lem3319178 A x s x')). Qed.
Lemma lem3319189 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3319251 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term46 A x s x') : term62 A x s x'.
Proof. exact (EQ_MP (@lem3319184 A x s x') (@lem3319137 A x s x' h1)). Qed.
Lemma lem3319252 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term63 A x s x') : term63 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3319253 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term59 A x s x') : term59 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3319255 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term63 A x s x') : term26 A s x' x.
Proof. exact (proj1 (@lem3319252 A x s x' h1)). Qed.
Lemma lem3319257 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term24 A s x' x) : term24 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3319261 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term59 A x s x') : term54 A s x' x.
Proof. exact (proj1 (@lem3319253 A x s x' h1)). Qed.
Lemma lem3319262 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term59 A x s x') : term50 A s x' x.
Proof. exact (proj2 (@lem3319261 A x s x' h1)). Qed.
Lemma lem3319269 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3319277 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3319309 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term64 A s x') : term64 A s x'.
Proof. exact (h1). Qed.
Lemma lem3319325 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3319327 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3319329 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term63 A x s x') : term64 A s x'.
Proof. exact (proj2 (@lem3319252 A x s x' h1)). Qed.
Lemma lem3319331 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3319335 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term63 A x s x') : term64 A s x'.
Proof. exact (proj2 (@lem3319252 A x s x' h1)). Qed.
Lemma lem3319347 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term64 A s x') : term64 A s x'.
Proof. exact (h1). Qed.
Lemma lem3319353 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term59 A x s x') : term23 A x' x.
Proof. exact (proj1 (@lem3319261 A x s x' h1)). Qed.
Lemma lem3319355 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3319383 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3319384 {A : Type'} (s : A -> Prop) : (term65 A s) = (term65 A s).
Proof. exact (eq_refl (term65 A s)). Qed.
Lemma lem3319385 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term66 A s x') = (term66 A s x).
Proof. exact (MK_COMB (@lem3319384 A s) (@lem3319331 A x' x h1)). Qed.
Lemma lem3319386 {A : Type'} (s : A -> Prop) (x : A) : (term66 A s x) = (term64 A s x).
Proof. exact (eq_refl (term66 A s x)). Qed.
Lemma lem3319387 {A : Type'} (s : A -> Prop) (x' : A) : (term67 A s x') = (term67 A s x').
Proof. exact (eq_refl (term67 A s x')). Qed.
Lemma lem3319388 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term66 A s x') = (term66 A s x)) = ((term66 A s x') = (term64 A s x)).
Proof. exact (MK_COMB (@lem3319387 A s x') (@lem3319386 A s x)). Qed.
Lemma lem3319389 {A : Type'} (s : A -> Prop) (x' : A) : (term66 A s x') = (term64 A s x').
Proof. exact (eq_refl (term66 A s x')). Qed.
Lemma lem3319390 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3319391 {A : Type'} (s : A -> Prop) (x' : A) : (term67 A s x') = (term68 A s x').
Proof. exact (MK_COMB (@lem3319390) (@lem3319389 A s x')). Qed.
Lemma lem3319392 {A : Type'} (s : A -> Prop) (x : A) : (term64 A s x) = (term64 A s x).
Proof. exact (eq_refl (term64 A s x)). Qed.
Lemma lem3319393 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term66 A s x') = (term64 A s x)) = ((term64 A s x') = (term64 A s x)).
Proof. exact (MK_COMB (@lem3319391 A s x') (@lem3319392 A s x)). Qed.
Lemma lem3319394 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term66 A s x') = (term66 A s x)) = ((term64 A s x') = (term64 A s x)).
Proof. exact (TRANS (@lem3319388 A x' s x) (@lem3319393 A x' s x)). Qed.
Lemma lem3319395 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term64 A s x') = (term64 A s x).
Proof. exact (EQ_MP (@lem3319394 A x' s x) (@lem3319385 A s x' x h1)). Qed.
Lemma lem3319396 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term63 A x s x') (h2 : x' = x) : term64 A s x.
Proof. exact (EQ_MP (@lem3319395 A s x' x h2) (@lem3319329 A x s x' h1)). Qed.
Lemma lem3319438 {A : Type'} (x : A) : (term69 A x) = (term69 A x).
Proof. exact (eq_refl (term69 A x)). Qed.
Lemma lem3319439 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term70 A x x') = (term71 A x).
Proof. exact (MK_COMB (@lem3319438 A x) (@lem3319355 A x' x h1)). Qed.
Lemma lem3319440 {A : Type'} (x : A) : (term71 A x) = (term72 A x).
Proof. exact (eq_refl (term71 A x)). Qed.
Lemma lem3319441 {A : Type'} (x : A) (x' : A) : (term73 A x x') = (term73 A x x').
Proof. exact (eq_refl (term73 A x x')). Qed.
Lemma lem3319442 {A : Type'} (x' : A) (x : A) : ((term70 A x x') = (term71 A x)) = ((term70 A x x') = (term72 A x)).
Proof. exact (MK_COMB (@lem3319441 A x x') (@lem3319440 A x)). Qed.
Lemma lem3319443 {A : Type'} (x' : A) (x : A) : (term70 A x x') = (term23 A x' x).
Proof. exact (eq_refl (term70 A x x')). Qed.
Lemma lem3319444 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3319445 {A : Type'} (x' : A) (x : A) : (term73 A x x') = (term74 A x' x).
Proof. exact (MK_COMB (@lem3319444) (@lem3319443 A x' x)). Qed.
Lemma lem3319446 {A : Type'} (x : A) : (term72 A x) = (term72 A x).
Proof. exact (eq_refl (term72 A x)). Qed.
Lemma lem3319447 {A : Type'} (x' : A) (x : A) : ((term70 A x x') = (term72 A x)) = ((term23 A x' x) = (term72 A x)).
Proof. exact (MK_COMB (@lem3319445 A x' x) (@lem3319446 A x)). Qed.
Lemma lem3319448 {A : Type'} (x' : A) (x : A) : ((term70 A x x') = (term71 A x)) = ((term23 A x' x) = (term72 A x)).
Proof. exact (TRANS (@lem3319442 A x' x) (@lem3319447 A x' x)). Qed.
Lemma lem3319449 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term23 A x' x) = (term72 A x).
Proof. exact (EQ_MP (@lem3319448 A x' x) (@lem3319439 A x' x h1)). Qed.
Lemma lem3319450 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term59 A x s x') (h2 : x' = x) : term72 A x.
Proof. exact (EQ_MP (@lem3319449 A x' x h2) (@lem3319353 A x s x' h1)). Qed.
Lemma lem3319452 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3319453 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term75 A s x.
Proof. exact (fun h0 : term64 A s x => @lem3319452 A s x h1). Qed.
Lemma lem3319455 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3319456 {A : Type'} (s : A -> Prop) (x : A) : (term75 A s x) = (s x).
Proof. exact (@lem3319455 (s x)). Qed.
Lemma lem3319457 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3319456 A s x) (@lem3319453 A s x h1)). Qed.
Lemma lem3319460 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3319462 {A : Type'} (s : A -> Prop) (x : A) : (term64 A s x) = (term77 A s x).
Proof. exact (@lem3319460 (s x)). Qed.
Lemma lem3319465 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term63 A x s x') (h2 : x' = x) : term77 A s x.
Proof. exact (EQ_MP (@lem3319462 A s x) (@lem3319396 A s x' x h1 h2)). Qed.
Lemma lem3319468 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term63 A x s x') (h3 : x' = x) : False.
Proof. exact (@lem3319465 A s x' x h2 h3 (@lem3319457 A s x h1)). Qed.
Lemma lem3319469 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term63 A x s x') (h3 : x' = x) : term78.
Proof. exact (fun h0 : ~ False => @lem3319468 A s x' x h1 h2 h3). Qed.
Lemma lem3319471 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3319472 : term78 = False.
Proof. exact (@lem3319471 False). Qed.
Lemma lem3319473 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term63 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3319472) (@lem3319469 A s x' x h1 h2 h3)). Qed.
Lemma lem3319489 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term24 A s x' x) : s x'.
Proof. exact (proj1 (@lem3319257 A s x' x h1)). Qed.
Lemma lem3319490 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term24 A s x' x) : term75 A s x'.
Proof. exact (fun h0 : term64 A s x' => @lem3319489 A s x' x h1). Qed.
Lemma lem3319492 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3319493 {A : Type'} (s : A -> Prop) (x' : A) : (term75 A s x') = (s x').
Proof. exact (@lem3319492 (s x')). Qed.
Lemma lem3319494 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term24 A s x' x) : s x'.
Proof. exact (EQ_MP (@lem3319493 A s x') (@lem3319490 A s x' x h1)). Qed.
Lemma lem3319497 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3319499 {A : Type'} (s : A -> Prop) (x' : A) : (term64 A s x') = (term77 A s x').
Proof. exact (@lem3319497 (s x')). Qed.
Lemma lem3319502 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term63 A x s x') : term77 A s x'.
Proof. exact (EQ_MP (@lem3319499 A s x') (@lem3319335 A x s x' h1)). Qed.
Lemma lem3319505 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term24 A s x' x) (h2 : term63 A x s x') : False.
Proof. exact (@lem3319502 A x s x' h2 (@lem3319494 A s x' x h1)). Qed.
Lemma lem3319506 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term24 A s x' x) (h2 : term63 A x s x') : term78.
Proof. exact (fun h0 : ~ False => @lem3319505 A x s x' h1 h2). Qed.
Lemma lem3319508 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3319509 : term78 = False.
Proof. exact (@lem3319508 False). Qed.
Lemma lem3319510 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term24 A s x' x) (h2 : term63 A x s x') : False.
Proof. exact (EQ_MP (@lem3319509) (@lem3319506 A x s x' h1 h2)). Qed.
Lemma lem3319526 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term59 A x s x') : s x'.
Proof. exact (proj2 (@lem3319253 A x s x' h1)). Qed.
Lemma lem3319527 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term59 A x s x') : term75 A s x'.
Proof. exact (fun h0 : term64 A s x' => @lem3319526 A x s x' h1). Qed.
Lemma lem3319529 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3319530 {A : Type'} (s : A -> Prop) (x' : A) : (term75 A s x') = (s x').
Proof. exact (@lem3319529 (s x')). Qed.
Lemma lem3319531 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term59 A x s x') : s x'.
Proof. exact (EQ_MP (@lem3319530 A s x') (@lem3319527 A x s x' h1)). Qed.
Lemma lem3319534 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3319536 {A : Type'} (s : A -> Prop) (x' : A) : (term64 A s x') = (term77 A s x').
Proof. exact (@lem3319534 (s x')). Qed.
Lemma lem3319539 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term64 A s x') : term77 A s x'.
Proof. exact (EQ_MP (@lem3319536 A s x') (@lem3319347 A s x' h1)). Qed.
Lemma lem3319542 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term64 A s x') (h2 : term59 A x s x') : False.
Proof. exact (@lem3319539 A s x' h1 (@lem3319531 A x s x' h2)). Qed.
Lemma lem3319543 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term64 A s x') (h2 : term59 A x s x') : term78.
Proof. exact (fun h0 : ~ False => @lem3319542 A x s x' h1 h2). Qed.
Lemma lem3319545 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3319546 : term78 = False.
Proof. exact (@lem3319545 False). Qed.
Lemma lem3319547 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term64 A s x') (h2 : term59 A x s x') : False.
Proof. exact (EQ_MP (@lem3319546) (@lem3319543 A x s x' h1 h2)). Qed.
Lemma lem3319563 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3319564 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3319563 A x). Qed.
Lemma lem3319565 {A : Type'} (x : A) : term79 A x.
Proof. exact (fun h0 : term72 A x => @lem3319564 A x). Qed.
Lemma lem3319567 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3319568 {A : Type'} (x : A) : (term79 A x) = (x = x).
Proof. exact (@lem3319567 (x = x)). Qed.
Lemma lem3319569 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3319568 A x) (@lem3319565 A x)). Qed.
Lemma lem3319572 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3319574 {A : Type'} (x : A) : (term72 A x) = (term80 A x).
Proof. exact (@lem3319572 (x = x)). Qed.
Lemma lem3319577 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term59 A x s x') (h2 : x' = x) : term80 A x.
Proof. exact (EQ_MP (@lem3319574 A x) (@lem3319450 A s x' x h1 h2)). Qed.
Lemma lem3319580 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term59 A x s x') (h2 : x' = x) : False.
Proof. exact (@lem3319577 A s x' x h1 h2 (@lem3319569 A x)). Qed.
Lemma lem3319581 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term59 A x s x') (h2 : x' = x) : term78.
Proof. exact (fun h0 : ~ False => @lem3319580 A s x' x h1 h2). Qed.
Lemma lem3319583 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3319584 : term78 = False.
Proof. exact (@lem3319583 False). Qed.
Lemma lem3319586 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term59 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3319584) (@lem3319581 A s x' x h1 h2)). Qed.
Lemma lem3319587 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term63 A x s x') (h3 : x' = x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3319473 A s x' x h1 h2 h3) (fun h4 : False => @lem3319383 A s x h1)). Qed.
Lemma lem3319589 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term63 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3319587 A s x' x h1 h2 h3) (@lem3319383 A s x h1)). Qed.
Lemma lem3319590 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term59 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3319586 A s x' x h1 h2) (fun h3 : False => @lem3319355 A x' x h2)). Qed.
Lemma lem3319591 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term59 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3319590 A s x' x h1 h2) (@lem3319355 A x' x h2)). Qed.
Lemma lem3319592 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term64 A s x') (h2 : term59 A x s x') : (term64 A s x') = False.
Proof. exact (prop_ext (fun h3 : term64 A s x' => @lem3319547 A x s x' h1 h2) (fun h3 : False => @lem3319347 A s x' h1)). Qed.
Lemma lem3319593 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term64 A s x') (h2 : term59 A x s x') : False.
Proof. exact (EQ_MP (@lem3319592 A x s x' h1 h2) (@lem3319347 A s x' h1)). Qed.
Lemma lem3319594 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term63 A x s x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3319589 A s x' x h1 h2 h3) (fun h4 : False => @lem3319331 A x' x h3)). Qed.
Lemma lem3319595 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term63 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3319594 A s x' x h1 h2 h3) (@lem3319331 A x' x h3)). Qed.
Lemma lem3319596 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term63 A x s x') (h3 : x' = x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3319595 A s x' x h1 h2 h3) (fun h4 : False => @lem3319327 A s x h1)). Qed.
Lemma lem3319597 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term63 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3319596 A s x' x h1 h2 h3) (@lem3319327 A s x h1)). Qed.
Lemma lem3319598 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term59 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3319591 A s x' x h1 h2) (fun h3 : False => @lem3319325 A x' x h2)). Qed.
Lemma lem3319599 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term59 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3319598 A s x' x h1 h2) (@lem3319325 A x' x h2)). Qed.
Lemma lem3319600 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term64 A s x') (h2 : term59 A x s x') : (term64 A s x') = False.
Proof. exact (prop_ext (fun h3 : term64 A s x' => @lem3319593 A x s x' h1 h2) (fun h3 : False => @lem3319309 A s x' h1)). Qed.
Lemma lem3319601 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term64 A s x') (h2 : term59 A x s x') : False.
Proof. exact (EQ_MP (@lem3319600 A x s x' h1 h2) (@lem3319309 A s x' h1)). Qed.
Lemma lem3319602 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term63 A x s x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3319597 A s x' x h1 h2 h3) (fun h4 : False => @lem3319277 A x' x h3)). Qed.
Lemma lem3319603 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term63 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3319602 A s x' x h1 h2 h3) (@lem3319277 A x' x h3)). Qed.
Lemma lem3319604 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term63 A x s x') (h3 : x' = x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3319603 A s x' x h1 h2 h3) (fun h4 : False => @lem3319269 A s x h1)). Qed.
Lemma lem3319605 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term63 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3319604 A s x' x h1 h2 h3) (@lem3319269 A s x h1)). Qed.
Lemma lem3319606 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term59 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3319599 A s x' x h1 h2) (fun h3 : False => @lem3319325 A x' x h2)). Qed.
Lemma lem3319607 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term59 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3319606 A s x' x h1 h2) (@lem3319325 A x' x h2)). Qed.
Lemma lem3319608 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term64 A s x') (h2 : term59 A x s x') : (term64 A s x') = False.
Proof. exact (prop_ext (fun h3 : term64 A s x' => @lem3319601 A x s x' h1 h2) (fun h3 : False => @lem3319309 A s x' h1)). Qed.
Lemma lem3319609 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term64 A s x') (h2 : term59 A x s x') : False.
Proof. exact (EQ_MP (@lem3319608 A x s x' h1 h2) (@lem3319309 A s x' h1)). Qed.
Lemma lem3319610 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term63 A x s x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3319605 A s x' x h1 h2 h3) (fun h4 : False => @lem3319277 A x' x h3)). Qed.
Lemma lem3319611 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term63 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3319610 A s x' x h1 h2 h3) (@lem3319277 A x' x h3)). Qed.
Lemma lem3319612 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term63 A x s x') (h3 : x' = x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3319611 A s x' x h1 h2 h3) (fun h4 : False => @lem3319269 A s x h1)). Qed.
Lemma lem3319613 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term63 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3319612 A s x' x h1 h2 h3) (@lem3319269 A s x h1)). Qed.
Lemma lem3319614 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term59 A x s x') : False.
Proof. exact (or_elim (@lem3319262 A x s x' h1) (fun h0 : term64 A s x' => @lem3319609 A x s x' h0 h1) (fun h0 : x' = x => @lem3319607 A s x' x h1 h0)). Qed.
Lemma lem3319615 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x) (h2 : term63 A x s x') : False.
Proof. exact (or_elim (@lem3319255 A x s x' h2) (fun h0 : x' = x => @lem3319613 A s x' x h1 h2 h0) (fun h0 : term24 A s x' x => @lem3319510 A x s x' h0 h2)). Qed.
Lemma lem3319616 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term46 A x s x') (h2 : s x) : False.
Proof. exact (or_elim (@lem3319251 A x s x' h1) (fun h0 : term63 A x s x' => @lem3319615 A x s x' h2 h0) (fun h0 : term59 A x s x' => @lem3319614 A x s x' h0)). Qed.
Lemma lem3319617 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term46 A x s x') (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3319616 A x' s x h1 h2) (fun h3 : False => @lem3319189 A s x h2)). Qed.
Lemma lem3319618 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term46 A x s x') (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3319617 A x' s x h1 h2) (@lem3319189 A s x h2)). Qed.
Lemma lem3319619 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term46 A x s x') (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3319618 A x' s x h1 h2) (fun h3 : False => @lem3319143 A s x h2)). Qed.
Lemma lem3319620 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term46 A x s x') (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3319619 A x' s x h1 h2) (@lem3319143 A s x h2)). Qed.
Lemma lem3319621 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term46 A x s x') (h2 : s x) : (term46 A x s x') = False.
Proof. exact (prop_ext (fun h3 : term46 A x s x' => @lem3319620 A x' s x h1 h2) (fun h3 : False => @lem3319137 A x s x' h1)). Qed.
Lemma lem3319622 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term46 A x s x') (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3319621 A x' s x h1 h2) (@lem3319137 A x s x' h1)). Qed.
Lemma lem3319623 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : s x) : term45 A x s x'.
Proof. exact (fun h0 : term46 A x s x' => @lem3319622 A x' s x h0 h1). Qed.
Lemma lem3319624 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : s x) : (term26 A s x' x) = (s x').
Proof. exact (EQ_MP (@lem3319136 A x s x') (@lem3319623 A x' s x h1)). Qed.
Lemma lem3319629 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term31 A x s.
Proof. exact (fun x' : A => @lem3319624 A x' s x h1). Qed.
Lemma lem3319630 {A : Type'} (x : A) (s : A -> Prop) : term32 A x s.
Proof. exact (fun h0 : s x => @lem3319629 A s x h0). Qed.
Lemma lem3319635 {A : Type'} (x : A) : term34 A x.
Proof. exact (fun s : A -> Prop => @lem3319630 A x s). Qed.
Lemma lem3319640 {A : Type'} : term36 A.
Proof. exact (fun x : A => @lem3319635 A x). Qed.
Lemma lem3319641 {A : Type'} : term38 A.
Proof. exact (EQ_MP (@lem3319131 A) (@lem3319640 A)). Qed.
Lemma lem3319643 {A : Type'} : term38 A.
Proof. exact (@lem3319046 A (@lem3319641 A)). Qed.
Lemma lem3319644 {A : Type'} (h1 : term39 A) : False.
Proof. exact (@lem3319643 A (@lem3319030 A h1)). Qed.
Lemma lem3319645 {A : Type'} (h1 : term39 A) : (term39 A) = False.
Proof. exact (prop_ext (fun h2 : term39 A => @lem3319644 A h1) (fun h2 : False => @lem3319030 A h1)). Qed.
Lemma lem3319646 {A : Type'} (h1 : term39 A) : False.
Proof. exact (EQ_MP (@lem3319645 A h1) (@lem3319030 A h1)). Qed.
Lemma lem3319647 {A : Type'} : term38 A.
Proof. exact (fun h0 : term39 A => @lem3319646 A h0). Qed.
Lemma lem3319648 {A : Type'} : term36 A.
Proof. exact (EQ_MP (@lem3319029 A) (@lem3319647 A)). Qed.
Lemma lem3319649 {A : Type'} : term13 A.
Proof. exact (EQ_MP (@lem3319025 A) (@lem3319648 A)). Qed.
Lemma lem3319650 {A : Type'} : term12 A.
Proof. exact (EQ_MP (@lem3318937 A) (@lem3319649 A)). Qed.
