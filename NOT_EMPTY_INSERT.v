Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NOT_EMPTY_INSERT_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17160_spec.
Require Import thm1857_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Lemma lem3278821 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3278822 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3278821 A s t). Qed.
Lemma lem3278823 {A : Type'} (x : A) (s : A -> Prop) : ((@EMPTY A) = (@INSERT A x s)) = (term1 A x s).
Proof. exact (@lem3278822 A (@EMPTY A) (@INSERT A x s)). Qed.
Lemma lem3278832 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3278833 {A : Type'} (x : A) (s : A -> Prop) : (term2 A x s) = (term3 A x s).
Proof. exact (MK_COMB (@lem3278832) (@lem3278823 A x s)). Qed.
Lemma lem3278834 {A : Type'} (x : A) : (term4 A x) = (term5 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3278833 A x s)). Qed.
Lemma lem3278835 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3278836 {A : Type'} (x : A) : (term6 A x) = (term7 A x).
Proof. exact (MK_COMB (@lem3278835 A) (@lem3278834 A x)). Qed.
Lemma lem3278841 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (fun_ext (fun x : A => @lem3278836 A x)). Qed.
Lemma lem3278842 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3278843 {A : Type'} : (term10 A) = (term11 A).
Proof. exact (MK_COMB (@lem3278842 A) (@lem3278841 A)). Qed.
Lemma lem3278848 {A : Type'} : (term11 A) = (term10 A).
Proof. exact (SYM (@lem3278843 A)). Qed.
Lemma lem3278864 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3278865 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3278864 A x). Qed.
Lemma lem3278866 {A : Type'} (x' : A) : (@IN A x' (@EMPTY A)) = False.
Proof. exact (@lem3278865 A x'). Qed.
Lemma lem3278867 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3278868 {A : Type'} (x' : A) : (term12 A x') = (@eq Prop False).
Proof. exact (MK_COMB (@lem3278867) (@lem3278866 A x')). Qed.
Lemma lem3278870 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term13 A x y s) = (term14 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3278871 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term13 A x y s) = (term14 A y x s).
Proof. exact (@lem3278870 A y x s). Qed.
Lemma lem3278872 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term13 A x' x s) = (term14 A x x' s).
Proof. exact (@lem3278871 A x x' s). Qed.
Lemma lem3278878 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3278879 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3278878 A P x). Qed.
Lemma lem3278880 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3278879 A s x'). Qed.
Lemma lem3278881 {A : Type'} (x' : A) (x : A) : (term15 A x' x) = (term15 A x' x).
Proof. exact (eq_refl (term15 A x' x)). Qed.
Lemma lem3278882 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term14 A x x' s) = (term16 A x s x').
Proof. exact (MK_COMB (@lem3278881 A x' x) (@lem3278880 A s x')). Qed.
Lemma lem3278885 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term13 A x' x s) = (term16 A x s x').
Proof. exact (TRANS (@lem3278872 A x x' s) (@lem3278882 A x s x')). Qed.
Lemma lem3278886 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((@IN A x' (@EMPTY A)) = (term13 A x' x s)) = (False = (term16 A x s x')).
Proof. exact (MK_COMB (@lem3278868 A x') (@lem3278885 A x s x')). Qed.
Lemma lem3278888 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem3278889 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (False = (term16 A x s x')) = (term17 A x s x').
Proof. exact (@lem3278888 (term16 A x s x')). Qed.
Lemma lem3278894 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((@IN A x' (@EMPTY A)) = (term13 A x' x s)) = (term17 A x s x').
Proof. exact (TRANS (@lem3278886 A x s x') (@lem3278889 A x s x')). Qed.
Lemma lem3278895 {A : Type'} (x : A) (s : A -> Prop) : (term18 A x s) = (term19 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3278894 A x s x')). Qed.
Lemma lem3278896 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3278897 {A : Type'} (x : A) (s : A -> Prop) : (term1 A x s) = (term20 A x s).
Proof. exact (MK_COMB (@lem3278896 A) (@lem3278895 A x s)). Qed.
Lemma lem3278902 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3278903 {A : Type'} (x : A) (s : A -> Prop) : (term3 A x s) = (term21 A x s).
Proof. exact (MK_COMB (@lem3278902) (@lem3278897 A x s)). Qed.
Lemma lem3278904 {A : Type'} (x : A) : (term5 A x) = (term22 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3278903 A x s)). Qed.
Lemma lem3278905 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3278906 {A : Type'} (x : A) : (term7 A x) = (term23 A x).
Proof. exact (MK_COMB (@lem3278905 A) (@lem3278904 A x)). Qed.
Lemma lem3278911 {A : Type'} : (term9 A) = (term24 A).
Proof. exact (fun_ext (fun x : A => @lem3278906 A x)). Qed.
Lemma lem3278912 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3278913 {A : Type'} : (term11 A) = (term25 A).
Proof. exact (MK_COMB (@lem3278912 A) (@lem3278911 A)). Qed.
Lemma lem3278918 {A : Type'} : (term25 A) = (term11 A).
Proof. exact (SYM (@lem3278913 A)). Qed.
Lemma lem3278920 (p : Prop) : p = (term26 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3278921 {A : Type'} : (term25 A) = (term27 A).
Proof. exact (@lem3278920 (term25 A)). Qed.
Lemma lem3278922 {A : Type'} : (term27 A) = (term25 A).
Proof. exact (SYM (@lem3278921 A)). Qed.
Lemma lem3278923 {A : Type'} (h1 : term28 A) : term28 A.
Proof. exact (h1). Qed.
Lemma lem3278926 {A : Type'} (h1 : term27 A) : term27 A.
Proof. exact (h1). Qed.
Lemma lem3278927 {A : Type'} : term29 A.
Proof. exact (fun h0 : term27 A => @lem3278926 A h0). Qed.
Lemma lem3278928 {A : Type'} (h1 : term29 A) : term29 A.
Proof. exact (h1). Qed.
Lemma lem3278929 {A : Type'} (h1 : term27 A) : term27 A.
Proof. exact (h1). Qed.
Lemma lem3278930 {A : Type'} (h1 : term27 A) (h2 : term29 A) : term27 A.
Proof. exact (@lem3278928 A h2 (@lem3278929 A h1)). Qed.
Lemma lem3278931 {A : Type'} (h1 : term27 A) : term30 A.
Proof. exact (fun h0 : term29 A => @lem3278930 A h1 h0). Qed.
Lemma lem3278932 {A : Type'} (h1 : term29 A) : term29 A.
Proof. exact (h1). Qed.
Lemma lem3278933 {A : Type'} (h1 : term27 A) (h2 : term29 A) : term27 A.
Proof. exact (@lem3278931 A h1 (@lem3278932 A h2)). Qed.
Lemma lem3278934 {A : Type'} (h1 : term29 A) : term29 A.
Proof. exact (fun h0 : term27 A => @lem3278933 A h0 h1). Qed.
Lemma lem3278935 {A : Type'} : term31 A.
Proof. exact (fun h0 : term29 A => @lem3278934 A h0). Qed.
Lemma lem3278938 {A : Type'} : term29 A.
Proof. exact (@lem3278935 A (@lem3278927 A)). Qed.
Lemma lem3278939 {A : Type'} : term29 A.
Proof. exact (@lem3278938 A). Qed.
Lemma lem3278941 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3278942 {A : Type'} : (term27 A) = (term32 A).
Proof. exact (@lem3278941 (term28 A)). Qed.
Lemma lem3278944 (t : Prop) : (term33 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3278945 {A : Type'} : (term32 A) = (term25 A).
Proof. exact (@lem3278944 (term25 A)). Qed.
Lemma lem3278964 {A : Type'} : (term27 A) = (term25 A).
Proof. exact (TRANS (@lem3278942 A) (@lem3278945 A)). Qed.
Lemma lem3278971 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term17 A x s x') = (term17 A x s x').
Proof. exact (eq_refl (term17 A x s x')). Qed.
Lemma lem3278972 {A : Type'} (x : A) (s : A -> Prop) : (term19 A x s) = (term19 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3278971 A x s x')). Qed.
Lemma lem3278973 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3278974 {A : Type'} (x : A) (s : A -> Prop) : (term20 A x s) = (term20 A x s).
Proof. exact (MK_COMB (@lem3278973 A) (@lem3278972 A x s)). Qed.
Lemma lem3278975 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3278976 {A : Type'} (x : A) (s : A -> Prop) : (term21 A x s) = (term21 A x s).
Proof. exact (MK_COMB (@lem3278975) (@lem3278974 A x s)). Qed.
Lemma lem3278977 {A : Type'} (x : A) : (term22 A x) = (term22 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3278976 A x s)). Qed.
Lemma lem3278978 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3278979 {A : Type'} (x : A) : (term23 A x) = (term23 A x).
Proof. exact (MK_COMB (@lem3278978 A) (@lem3278977 A x)). Qed.
Lemma lem3278980 {A : Type'} : (term24 A) = (term24 A).
Proof. exact (fun_ext (fun x : A => @lem3278979 A x)). Qed.
Lemma lem3278981 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3278982 {A : Type'} : (term25 A) = (term25 A).
Proof. exact (MK_COMB (@lem3278981 A) (@lem3278980 A)). Qed.
Lemma lem3279005 {A : Type'} : (term27 A) = (term25 A).
Proof. exact (TRANS (@lem3278964 A) (@lem3278982 A)). Qed.
Lemma lem3279006 {A : Type'} : (term25 A) = (term27 A).
Proof. exact (SYM (@lem3279005 A)). Qed.
Lemma lem3279007 {A : Type'} (x : A) (s : A -> Prop) (h1 : term20 A x s) : term20 A x s.
Proof. exact (h1). Qed.
Lemma lem3279014 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term17 A x s x') = (term34 A x s x').
Proof. exact (@lem17160 (x' = x) (s x')). Qed.
Lemma lem3279015 {A : Type'} (x : A) (s : A -> Prop) : (term19 A x s) = (term35 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3279014 A x s x')). Qed.
Lemma lem3279016 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3279017 {A : Type'} (x : A) (s : A -> Prop) : (term20 A x s) = (term36 A x s).
Proof. exact (MK_COMB (@lem3279016 A) (@lem3279015 A x s)). Qed.
Lemma lem3279019 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term37 A P Q) = (term38 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3279020 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term37 A P Q) = (term38 A P Q).
Proof. exact (@lem3279019 A P Q). Qed.
Lemma lem3279021 {A : Type'} (x : A) (s : A -> Prop) : (term39 A x s) = (term40 A x s).
Proof. exact (@lem3279020 A (term41 A x) (term42 A s)). Qed.
Lemma lem3279022 {A : Type'} (x' : A) (x : A) : (term43 A x x') = (term44 A x' x).
Proof. exact (eq_refl (term43 A x x')). Qed.
Lemma lem3279023 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3279024 {A : Type'} (x' : A) (x : A) : (term45 A x x') = (term46 A x' x).
Proof. exact (MK_COMB (@lem3279023) (@lem3279022 A x' x)). Qed.
Lemma lem3279025 {A : Type'} (s : A -> Prop) (x' : A) : (term47 A s x') = (term48 A s x').
Proof. exact (eq_refl (term47 A s x')). Qed.
Lemma lem3279026 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term49 A x s x') = (term34 A x s x').
Proof. exact (MK_COMB (@lem3279024 A x' x) (@lem3279025 A s x')). Qed.
Lemma lem3279027 {A : Type'} (x : A) (s : A -> Prop) : (term50 A x s) = (term35 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3279026 A x s x')). Qed.
Lemma lem3279028 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3279029 {A : Type'} (x : A) (s : A -> Prop) : (term39 A x s) = (term36 A x s).
Proof. exact (MK_COMB (@lem3279028 A) (@lem3279027 A x s)). Qed.
Lemma lem3279030 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3279031 {A : Type'} (x : A) (s : A -> Prop) : (term51 A x s) = (term52 A x s).
Proof. exact (MK_COMB (@lem3279030) (@lem3279029 A x s)). Qed.
Lemma lem3279032 {A : Type'} (x' : A) (x : A) : (term43 A x x') = (term44 A x' x).
Proof. exact (eq_refl (term43 A x x')). Qed.
Lemma lem3279033 {A : Type'} (x : A) : (term53 A x) = (term41 A x).
Proof. exact (fun_ext (fun x' : A => @lem3279032 A x' x)). Qed.
Lemma lem3279034 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3279035 {A : Type'} (x : A) : (term54 A x) = (term55 A x).
Proof. exact (MK_COMB (@lem3279034 A) (@lem3279033 A x)). Qed.
Lemma lem3279036 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3279037 {A : Type'} (x : A) : (term56 A x) = (term57 A x).
Proof. exact (MK_COMB (@lem3279036) (@lem3279035 A x)). Qed.
Lemma lem3279038 {A : Type'} (s : A -> Prop) (x' : A) : (term47 A s x') = (term48 A s x').
Proof. exact (eq_refl (term47 A s x')). Qed.
Lemma lem3279039 {A : Type'} (s : A -> Prop) : (term58 A s) = (term42 A s).
Proof. exact (fun_ext (fun x' : A => @lem3279038 A s x')). Qed.
Lemma lem3279040 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3279041 {A : Type'} (s : A -> Prop) : (term59 A s) = (term60 A s).
Proof. exact (MK_COMB (@lem3279040 A) (@lem3279039 A s)). Qed.
Lemma lem3279042 {A : Type'} (x : A) (s : A -> Prop) : (term40 A x s) = (term61 A x s).
Proof. exact (MK_COMB (@lem3279037 A x) (@lem3279041 A s)). Qed.
Lemma lem3279043 {A : Type'} (x : A) (s : A -> Prop) : ((term39 A x s) = (term40 A x s)) = ((term36 A x s) = (term61 A x s)).
Proof. exact (MK_COMB (@lem3279031 A x s) (@lem3279042 A x s)). Qed.
Lemma lem3279054 {A : Type'} (x : A) (s : A -> Prop) : (term36 A x s) = (term61 A x s).
Proof. exact (EQ_MP (@lem3279043 A x s) (@lem3279021 A x s)). Qed.
Lemma lem3279055 {A : Type'} (x : A) (s : A -> Prop) : (term20 A x s) = (term61 A x s).
Proof. exact (TRANS (@lem3279017 A x s) (@lem3279054 A x s)). Qed.
Lemma lem3279056 {A : Type'} (x : A) (s : A -> Prop) (h1 : term20 A x s) : term61 A x s.
Proof. exact (EQ_MP (@lem3279055 A x s) (@lem3279007 A x s h1)). Qed.
Lemma lem3279061 {A : Type'} (s : A -> Prop) (x' : A) : (term48 A s x') = (term48 A s x').
Proof. exact (eq_refl (term48 A s x')). Qed.
Lemma lem3279062 {A : Type'} (s : A -> Prop) : (term42 A s) = (term42 A s).
Proof. exact (fun_ext (fun x' : A => @lem3279061 A s x')). Qed.
Lemma lem3279063 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3279064 {A : Type'} (s : A -> Prop) : (term60 A s) = (term60 A s).
Proof. exact (MK_COMB (@lem3279063 A) (@lem3279062 A s)). Qed.
Lemma lem3279071 {A : Type'} (x' : A) (x : A) : (term44 A x' x) = (term44 A x' x).
Proof. exact (eq_refl (term44 A x' x)). Qed.
Lemma lem3279072 {A : Type'} (x : A) : (term41 A x) = (term41 A x).
Proof. exact (fun_ext (fun x' : A => @lem3279071 A x' x)). Qed.
Lemma lem3279073 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3279074 {A : Type'} (x : A) : (term55 A x) = (term55 A x).
Proof. exact (MK_COMB (@lem3279073 A) (@lem3279072 A x)). Qed.
Lemma lem3279075 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3279076 {A : Type'} (x : A) : (term57 A x) = (term57 A x).
Proof. exact (MK_COMB (@lem3279075) (@lem3279074 A x)). Qed.
Lemma lem3279077 {A : Type'} (x : A) (s : A -> Prop) : (term61 A x s) = (term61 A x s).
Proof. exact (MK_COMB (@lem3279076 A x) (@lem3279064 A s)). Qed.
Lemma lem3279078 {A : Type'} (x : A) (s : A -> Prop) (h1 : term20 A x s) : term61 A x s.
Proof. exact (EQ_MP (@lem3279077 A x s) (@lem3279056 A x s h1)). Qed.
Lemma lem3279080 {A : Type'} (x : A) (s : A -> Prop) (h1 : term20 A x s) : term55 A x.
Proof. exact (proj1 (@lem3279078 A x s h1)). Qed.
Lemma lem3279082 {A : Type'} (x' : A) (x : A) : (term44 A x' x) = (term44 A x' x).
Proof. exact (eq_refl (term44 A x' x)). Qed.
Lemma lem3279083 {A : Type'} (x : A) : (term41 A x) = (term41 A x).
Proof. exact (fun_ext (fun x' : A => @lem3279082 A x' x)). Qed.
Lemma lem3279084 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3279086 {A : Type'} (x : A) : (term55 A x) = (term55 A x).
Proof. exact (MK_COMB (@lem3279084 A) (@lem3279083 A x)). Qed.
Lemma lem3279087 {A : Type'} (x : A) (s : A -> Prop) (h1 : term20 A x s) : term55 A x.
Proof. exact (EQ_MP (@lem3279086 A x) (@lem3279080 A x s h1)). Qed.
Lemma lem3279095 {A : Type'} (_33582 : A) (x : A) (s : A -> Prop) (h1 : term20 A x s) : term43 A x _33582.
Proof. exact (@lem3279087 A x s h1 _33582). Qed.
Lemma lem3279096 {A : Type'} (_33582 : A) (x : A) : (term43 A x _33582) = (term44 A _33582 x).
Proof. exact (eq_refl (term43 A x _33582)). Qed.
Lemma lem3279102 {A : Type'} (_33582 : A) (x : A) (s : A -> Prop) (h1 : term20 A x s) : term44 A _33582 x.
Proof. exact (EQ_MP (@lem3279096 A _33582 x) (@lem3279095 A _33582 x s h1)). Qed.
Lemma lem3279120 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3279121 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3279120 A x). Qed.
Lemma lem3279122 {A : Type'} (x : A) : term62 A x.
Proof. exact (fun h0 : term63 A x => @lem3279121 A x). Qed.
Lemma lem3279124 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3279125 {A : Type'} (x : A) : (term62 A x) = (x = x).
Proof. exact (@lem3279124 (x = x)). Qed.
Lemma lem3279126 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3279125 A x) (@lem3279122 A x)). Qed.
Lemma lem3279129 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3279131 {A : Type'} (_33582 : A) (x : A) : (term44 A _33582 x) = (term65 A _33582 x).
Proof. exact (@lem3279129 (_33582 = x)). Qed.
Lemma lem3279134 {A : Type'} (_33582 : A) (x : A) (s : A -> Prop) (h1 : term20 A x s) : term65 A _33582 x.
Proof. exact (EQ_MP (@lem3279131 A _33582 x) (@lem3279102 A _33582 x s h1)). Qed.
Lemma lem3279135 {A : Type'} (_33582 : A) (x : A) (s : A -> Prop) (h1 : term20 A x s) : term65 A _33582 x.
Proof. exact (@lem3279134 A _33582 x s h1). Qed.
Lemma lem3279136 {A : Type'} (x : A) (s : A -> Prop) (h1 : term20 A x s) : term66 A x.
Proof. exact (@lem3279135 A x x s h1). Qed.
Lemma lem3279139 {A : Type'} (x : A) (s : A -> Prop) (h1 : term20 A x s) : False.
Proof. exact (@lem3279136 A x s h1 (@lem3279126 A x)). Qed.
Lemma lem3279140 {A : Type'} (x : A) (s : A -> Prop) (h1 : term20 A x s) : term67.
Proof. exact (fun h0 : ~ False => @lem3279139 A x s h1). Qed.
Lemma lem3279142 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3279143 : term67 = False.
Proof. exact (@lem3279142 False). Qed.
Lemma lem3279144 {A : Type'} (x : A) (s : A -> Prop) (h1 : term20 A x s) : False.
Proof. exact (EQ_MP (@lem3279143) (@lem3279140 A x s h1)). Qed.
Lemma lem3279145 {A : Type'} (x : A) (s : A -> Prop) : term68 A x s.
Proof. exact (fun h0 : term20 A x s => @lem3279144 A x s h0). Qed.
Lemma lem3279146 {A : Type'} (x : A) (s : A -> Prop) : (term68 A x s) = (term21 A x s).
Proof. exact (@lem69 (term20 A x s)). Qed.
Lemma lem3279147 {A : Type'} (x : A) (s : A -> Prop) : term21 A x s.
Proof. exact (EQ_MP (@lem3279146 A x s) (@lem3279145 A x s)). Qed.
Lemma lem3279152 {A : Type'} (x : A) : term23 A x.
Proof. exact (fun s : A -> Prop => @lem3279147 A x s). Qed.
Lemma lem3279157 {A : Type'} : term25 A.
Proof. exact (fun x : A => @lem3279152 A x). Qed.
Lemma lem3279158 {A : Type'} : term27 A.
Proof. exact (EQ_MP (@lem3279006 A) (@lem3279157 A)). Qed.
Lemma lem3279160 {A : Type'} : term27 A.
Proof. exact (@lem3278939 A (@lem3279158 A)). Qed.
Lemma lem3279161 {A : Type'} (h1 : term28 A) : False.
Proof. exact (@lem3279160 A (@lem3278923 A h1)). Qed.
Lemma lem3279162 {A : Type'} (h1 : term28 A) : (term28 A) = False.
Proof. exact (prop_ext (fun h2 : term28 A => @lem3279161 A h1) (fun h2 : False => @lem3278923 A h1)). Qed.
Lemma lem3279163 {A : Type'} (h1 : term28 A) : False.
Proof. exact (EQ_MP (@lem3279162 A h1) (@lem3278923 A h1)). Qed.
Lemma lem3279164 {A : Type'} : term27 A.
Proof. exact (fun h0 : term28 A => @lem3279163 A h0). Qed.
Lemma lem3279165 {A : Type'} : term25 A.
Proof. exact (EQ_MP (@lem3278922 A) (@lem3279164 A)). Qed.
Lemma lem3279166 {A : Type'} : term11 A.
Proof. exact (EQ_MP (@lem3278918 A) (@lem3279165 A)). Qed.
Lemma lem3279167 {A : Type'} : term10 A.
Proof. exact (EQ_MP (@lem3278848 A) (@lem3279166 A)). Qed.
