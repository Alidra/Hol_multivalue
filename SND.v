Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SND_term_abbrevs.
Require Import PAIR_EQ_spec.
Require Import SELECT_UNIQUE_spec.
Require Import SND_DEF_spec.
Require Import thm0_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Lemma lem47828 {A B : Type'} (x : A) : term0 A B x.
Proof. exact (@lem47438 A B x). Qed.
Lemma lem47829 {A B : Type'} (x : A) : (term0 A B x) = (term1 A B x).
Proof. exact (eq_refl (term0 A B x)). Qed.
Lemma lem47830 {A B : Type'} (x : A) : term1 A B x.
Proof. exact (EQ_MP (@lem47829 A B x) (@lem47828 A B x)). Qed.
Lemma lem47831 {A B : Type'} (x : A) (y : B) : term2 A B x y.
Proof. exact (@lem47830 A B x y). Qed.
Lemma lem47832 {A B : Type'} (x : A) (y : B) : (term2 A B x y) = (term3 A B x y).
Proof. exact (eq_refl (term2 A B x y)). Qed.
Lemma lem47833 {A B : Type'} (x : A) (y : B) : term3 A B x y.
Proof. exact (EQ_MP (@lem47832 A B x y) (@lem47831 A B x y)). Qed.
Lemma lem47834 {A B : Type'} (x : A) (y : B) (a : A) : term4 A B x y a.
Proof. exact (@lem47833 A B x y a). Qed.
Lemma lem47835 {A B : Type'} (x : A) (a : A) (y : B) : (term4 A B x y a) = (term5 A B x a y).
Proof. exact (eq_refl (term4 A B x y a)). Qed.
Lemma lem47836 {A B : Type'} (x : A) (a : A) (y : B) : term5 A B x a y.
Proof. exact (EQ_MP (@lem47835 A B x a y) (@lem47834 A B x y a)). Qed.
Lemma lem47837 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : term6 A B x a y b.
Proof. exact (@lem47836 A B x a y b). Qed.
Lemma lem47838 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term6 A B x a y b) = (((@pair A B x y) = (@pair A B a b)) = (term7 A B x a y b)).
Proof. exact (eq_refl (term6 A B x a y b)). Qed.
Lemma lem47840 {A : Type'} (h1 : term8 A) : term8 A.
Proof. exact (h1). Qed.
Lemma lem47841 {A : Type'} (P : A -> Prop) (h1 : term8 A) : term9 A P.
Proof. exact (@lem47840 A h1 P). Qed.
Lemma lem47842 {A : Type'} (P : A -> Prop) : (term9 A P) = (term10 A P).
Proof. exact (eq_refl (term9 A P)). Qed.
Lemma lem47843 {A : Type'} (P : A -> Prop) (h1 : term8 A) : term10 A P.
Proof. exact (EQ_MP (@lem47842 A P) (@lem47841 A P h1)). Qed.
Lemma lem47844 {A : Type'} (P : A -> Prop) (x : A) (h1 : term8 A) : term11 A P x.
Proof. exact (@lem47843 A P h1 x). Qed.
Lemma lem47845 {A : Type'} (P : A -> Prop) (x : A) : (term11 A P x) = (term12 A P x).
Proof. exact (eq_refl (term11 A P x)). Qed.
Lemma lem47846 {A : Type'} (P : A -> Prop) (x : A) (h1 : term8 A) : term12 A P x.
Proof. exact (EQ_MP (@lem47845 A P x) (@lem47844 A P x h1)). Qed.
Lemma lem47847 {A : Type'} (P : A -> Prop) (x : A) (h1 : term13 A P x) : term13 A P x.
Proof. exact (h1). Qed.
Lemma lem47848 {A : Type'} (P : A -> Prop) (x : A) (h1 : term13 A P x) (h2 : term8 A) : (@ε A P) = x.
Proof. exact (@lem47846 A P x h2 (@lem47847 A P x h1)). Qed.
Lemma lem47849 {A : Type'} (P : A -> Prop) (x : A) (h1 : term13 A P x) : term14 A P x.
Proof. exact (fun h0 : term8 A => @lem47848 A P x h1 h0). Qed.
Lemma lem47850 {A : Type'} (h1 : term8 A) : term8 A.
Proof. exact (h1). Qed.
Lemma lem47851 {A : Type'} (P : A -> Prop) (x : A) (h1 : term13 A P x) (h2 : term8 A) : (@ε A P) = x.
Proof. exact (@lem47849 A P x h1 (@lem47850 A h2)). Qed.
Lemma lem47852 {A : Type'} (P : A -> Prop) (x : A) (h1 : term8 A) : term12 A P x.
Proof. exact (fun h0 : term13 A P x => @lem47851 A P x h0 h1). Qed.
Lemma lem47853 {A : Type'} (P : A -> Prop) (h1 : term8 A) : term10 A P.
Proof. exact (fun x : A => @lem47852 A P x h1). Qed.
Lemma lem47854 {A : Type'} (h1 : term8 A) : term8 A.
Proof. exact (fun P : A -> Prop => @lem47853 A P h1). Qed.
Lemma lem47855 {A : Type'} : term15 A.
Proof. exact (fun h0 : term8 A => @lem47854 A h0). Qed.
Lemma lem47856 {A : Type'} : term8 A.
Proof. exact (@lem47855 A (@lem9522 A)). Qed.
Lemma lem47857 {A : Type'} (P : A -> Prop) : term9 A P.
Proof. exact (@lem47856 A P). Qed.
Lemma lem47858 {A : Type'} (P : A -> Prop) : (term9 A P) = (term10 A P).
Proof. exact (eq_refl (term9 A P)). Qed.
Lemma lem47859 {A : Type'} (P : A -> Prop) : term10 A P.
Proof. exact (EQ_MP (@lem47858 A P) (@lem47857 A P)). Qed.
Lemma lem47860 {A : Type'} (P : A -> Prop) (x : A) : term11 A P x.
Proof. exact (@lem47859 A P x). Qed.
Lemma lem47861 {A : Type'} (P : A -> Prop) (x : A) : (term11 A P x) = (term12 A P x).
Proof. exact (eq_refl (term11 A P x)). Qed.
Lemma lem47863 {A B : Type'} (p : prod A B) : term16 A B p.
Proof. exact (@lem45478 A B p). Qed.
Lemma lem47864 {A B : Type'} (p : prod A B) : (term16 A B p) = ((@snd A B p) = (term17 A B p)).
Proof. exact (eq_refl (term16 A B p)). Qed.
Lemma lem47869 {A B : Type'} (p : prod A B) : (@snd A B p) = (term17 A B p).
Proof. exact (EQ_MP (@lem47864 A B p) (@lem47863 A B p)). Qed.
Lemma lem47870 {A B : Type'} (p : prod A B) : (@snd A B p) = (term17 A B p).
Proof. exact (@lem47869 A B p). Qed.
Lemma lem47871 {A B : Type'} (x : A) (y : B) : (term18 A B x y) = (term19 A B x y).
Proof. exact (@lem47870 A B (@pair A B x y)). Qed.
Lemma lem47878 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem47879 {A B : Type'} (x : A) (y : B) : (term20 A B x y) = (term21 A B x y).
Proof. exact (MK_COMB (@lem47878 B) (@lem47871 A B x y)). Qed.
Lemma lem47880 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem47881 {A B : Type'} (x : A) (y : B) : ((term18 A B x y) = y) = ((term19 A B x y) = y).
Proof. exact (MK_COMB (@lem47879 A B x y) (@lem47880 B y)). Qed.
Lemma lem47884 {A B : Type'} (x : A) (y : B) : ((term19 A B x y) = y) = ((term18 A B x y) = y).
Proof. exact (SYM (@lem47881 A B x y)). Qed.
Lemma lem47886 {A : Type'} (P : A -> Prop) (x : A) : term12 A P x.
Proof. exact (EQ_MP (@lem47861 A P x) (@lem47860 A P x)). Qed.
Lemma lem47887 {B : Type'} (P : B -> Prop) (x : B) : term12 B P x.
Proof. exact (@lem47886 B P x). Qed.
Lemma lem47888 {A B : Type'} (x : A) (y : B) : term22 A B x y.
Proof. exact (@lem47887 B (term23 A B x y) y). Qed.
Lemma lem47889 {A B : Type'} (x : A) (y : B) (y' : B) : (term24 A B x y y') = (term25 A B x y y').
Proof. exact (eq_refl (term24 A B x y y')). Qed.
Lemma lem47890 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem47891 {A B : Type'} (x : A) (y : B) (y' : B) : (term26 A B x y y') = (term27 A B x y y').
Proof. exact (MK_COMB (@lem47890) (@lem47889 A B x y y')). Qed.
Lemma lem47892 {B : Type'} (y' : B) (y : B) : (y' = y) = (y' = y).
Proof. exact (eq_refl (y' = y)). Qed.
Lemma lem47893 {A B : Type'} (x : A) (y' : B) (y : B) : ((term24 A B x y y') = (y' = y)) = ((term25 A B x y y') = (y' = y)).
Proof. exact (MK_COMB (@lem47891 A B x y y') (@lem47892 B y' y)). Qed.
Lemma lem47894 {A B : Type'} (x : A) (y' : B) (y : B) : ((term25 A B x y y') = (y' = y)) = ((term24 A B x y y') = (y' = y)).
Proof. exact (SYM (@lem47893 A B x y' y)). Qed.
Lemma lem47902 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : ((@pair A B x y) = (@pair A B a b)) = (term7 A B x a y b).
Proof. exact (EQ_MP (@lem47838 A B x a y b) (@lem47837 A B x a y b)). Qed.
Lemma lem47903 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : ((@pair A B x y) = (@pair A B a b)) = (term7 A B x a y b).
Proof. exact (@lem47902 A B x a y b). Qed.
Lemma lem47904 {A B : Type'} (x : A) (x' : A) (y : B) (y' : B) : ((@pair A B x y) = (@pair A B x' y')) = (term7 A B x x' y y').
Proof. exact (@lem47903 A B x x' y y'). Qed.
Lemma lem47911 {A B : Type'} (x : A) (y : B) (y' : B) : (term28 A B x y y') = (term29 A B x y y').
Proof. exact (fun_ext (fun x' : A => @lem47904 A B x x' y y')). Qed.
Lemma lem47912 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem47913 {A B : Type'} (x : A) (y : B) (y' : B) : (term25 A B x y y') = (term30 A B x y y').
Proof. exact (MK_COMB (@lem47912 A) (@lem47911 A B x y y')). Qed.
Lemma lem47918 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem47919 {A B : Type'} (x : A) (y : B) (y' : B) : (term27 A B x y y') = (term31 A B x y y').
Proof. exact (MK_COMB (@lem47918) (@lem47913 A B x y y')). Qed.
Lemma lem47922 {B : Type'} (y' : B) (y : B) : (y' = y) = (y' = y).
Proof. exact (eq_refl (y' = y)). Qed.
Lemma lem47923 {A B : Type'} (x : A) (y' : B) (y : B) : ((term25 A B x y y') = (y' = y)) = ((term30 A B x y y') = (y' = y)).
Proof. exact (MK_COMB (@lem47919 A B x y y') (@lem47922 B y' y)). Qed.
Lemma lem47926 {A B : Type'} (x : A) (y' : B) (y : B) : ((term30 A B x y y') = (y' = y)) = ((term25 A B x y y') = (y' = y)).
Proof. exact (SYM (@lem47923 A B x y' y)). Qed.
Lemma lem47927 {A B : Type'} (x : A) (y : B) (y' : B) (h1 : term30 A B x y y') : term30 A B x y y'.
Proof. exact (h1). Qed.
Lemma lem47928 {A B : Type'} (x : A) (x' : A) (y : B) (y' : B) (h1 : term7 A B x x' y y') : term7 A B x x' y y'.
Proof. exact (h1). Qed.
Lemma lem47929 {B : Type'} (y : B) (y' : B) (h1 : y = y') : y = y'.
Proof. exact (h1). Qed.
Lemma lem47931 {B : Type'} (y' : B) (y : B) (h1 : y' = y) : y' = y.
Proof. exact (h1). Qed.
Lemma lem47935 {B : Type'} (y : B) (y' : B) (h1 : y = y') : y = y'.
Proof. exact (h1). Qed.
Lemma lem47936 {B : Type'} (y' : B) : (@eq B y') = (@eq B y').
Proof. exact (eq_refl (@eq B y')). Qed.
Lemma lem47937 {B : Type'} (y : B) (y' : B) (h1 : y = y') : (y' = y) = (y' = y').
Proof. exact (MK_COMB (@lem47936 B y') (@lem47935 B y y' h1)). Qed.
Lemma lem47939 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem47940 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem47939 B x). Qed.
Lemma lem47941 {B : Type'} (y' : B) : (y' = y') = True.
Proof. exact (@lem47940 B y'). Qed.
Lemma lem47942 {B : Type'} (y : B) (y' : B) (h1 : y = y') : (y' = y) = True.
Proof. exact (TRANS (@lem47937 B y y' h1) (@lem47941 B y')). Qed.
Lemma lem47943 {B : Type'} (y : B) (y' : B) (h1 : y = y') : True = (y' = y).
Proof. exact (SYM (@lem47942 B y y' h1)). Qed.
Lemma lem47944 {B : Type'} (y : B) (y' : B) (h1 : y = y') : y' = y.
Proof. exact (EQ_MP (@lem47943 B y y' h1) (@lem0)). Qed.
Lemma lem47956 {B : Type'} (y' : B) (y : B) (h1 : y' = y) : y' = y.
Proof. exact (h1). Qed.
Lemma lem47957 {B : Type'} (y : B) : (@eq B y) = (@eq B y).
Proof. exact (eq_refl (@eq B y)). Qed.
Lemma lem47958 {B : Type'} (y' : B) (y : B) (h1 : y' = y) : (y = y') = (y = y).
Proof. exact (MK_COMB (@lem47957 B y) (@lem47956 B y' y h1)). Qed.
Lemma lem47960 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem47961 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem47960 B x). Qed.
Lemma lem47962 {B : Type'} (y : B) : (y = y) = True.
Proof. exact (@lem47961 B y). Qed.
Lemma lem47963 {B : Type'} (y' : B) (y : B) (h1 : y' = y) : (y = y') = True.
Proof. exact (TRANS (@lem47958 B y' y h1) (@lem47962 B y)). Qed.
Lemma lem47964 {A : Type'} (x : A) (x' : A) : (term32 A x x') = (term32 A x x').
Proof. exact (eq_refl (term32 A x x')). Qed.
Lemma lem47965 {A B : Type'} (x : A) (x' : A) (y' : B) (y : B) (h1 : y' = y) : (term7 A B x x' y y') = (term33 A x x').
Proof. exact (MK_COMB (@lem47964 A x x') (@lem47963 B y' y h1)). Qed.
Lemma lem47967 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem47968 {A : Type'} (x : A) (x' : A) : (term33 A x x') = (x = x').
Proof. exact (@lem47967 (x = x')). Qed.
Lemma lem47971 {A B : Type'} (x : A) (x' : A) (y' : B) (y : B) (h1 : y' = y) : (term7 A B x x' y y') = (x = x').
Proof. exact (TRANS (@lem47965 A B x x' y' y h1) (@lem47968 A x x')). Qed.
Lemma lem47972 {A B : Type'} (x : A) (y' : B) (y : B) (h1 : y' = y) : (term29 A B x y y') = (term34 A x).
Proof. exact (fun_ext (fun x' : A => @lem47971 A B x x' y' y h1)). Qed.
Lemma lem47973 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem47974 {A B : Type'} (x : A) (y' : B) (y : B) (h1 : y' = y) : (term30 A B x y y') = (term35 A x).
Proof. exact (MK_COMB (@lem47973 A) (@lem47972 A B x y' y h1)). Qed.
Lemma lem47979 {A B : Type'} (x : A) (y' : B) (y : B) (h1 : y' = y) : (term35 A x) = (term30 A B x y y').
Proof. exact (SYM (@lem47974 A B x y' y h1)). Qed.
Lemma lem47981 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem47982 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem47981 A x). Qed.
Lemma lem47983 {A : Type'} (x : A) : True = (x = x).
Proof. exact (SYM (@lem47982 A x)). Qed.
Lemma lem47984 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem47983 A x) (@lem0)). Qed.
Lemma lem47985 {A : Type'} (x : A) : term35 A x.
Proof. exact (ex_intro (term34 A x) x (@lem47984 A x)). Qed.
Lemma lem47986 {A B : Type'} (x : A) (y' : B) (y : B) (h1 : y' = y) : term30 A B x y y'.
Proof. exact (EQ_MP (@lem47979 A B x y' y h1) (@lem47985 A x)). Qed.
Lemma lem47987 {A B : Type'} (x : A) (y' : B) (y : B) (h1 : y' = y) : (y' = y) = (term30 A B x y y').
Proof. exact (prop_ext (fun h2 : y' = y => @lem47986 A B x y' y h1) (fun h2 : term30 A B x y y' => @lem47931 B y' y h1)). Qed.
Lemma lem47988 {A B : Type'} (x : A) (y' : B) (y : B) (h1 : y' = y) : term30 A B x y y'.
Proof. exact (EQ_MP (@lem47987 A B x y' y h1) (@lem47931 B y' y h1)). Qed.
Lemma lem47989 {A B : Type'} (x : A) (y : B) (y' : B) : term36 A B x y y'.
Proof. exact (fun h0 : y' = y => @lem47988 A B x y' y h0). Qed.
Lemma lem47990 {A B : Type'} (x : A) (x' : A) (y : B) (y' : B) (h1 : term7 A B x x' y y') : y = y'.
Proof. exact (proj2 (@lem47928 A B x x' y y' h1)). Qed.
Lemma lem47992 {B : Type'} (y : B) (y' : B) (h1 : y = y') : (y = y') = (y' = y).
Proof. exact (prop_ext (fun h2 : y = y' => @lem47944 B y y' h1) (fun h2 : y' = y => @lem47929 B y y' h1)). Qed.
Lemma lem47993 {B : Type'} (y : B) (y' : B) (h1 : y = y') : y' = y.
Proof. exact (EQ_MP (@lem47992 B y y' h1) (@lem47929 B y y' h1)). Qed.
Lemma lem47994 {A B : Type'} (x : A) (x' : A) (y : B) (y' : B) (h1 : term7 A B x x' y y') : (y = y') = (y' = y).
Proof. exact (prop_ext (fun h2 : y = y' => @lem47993 B y y' h2) (fun h2 : y' = y => @lem47990 A B x x' y y' h1)). Qed.
Lemma lem47995 {A B : Type'} (x : A) (x' : A) (y : B) (y' : B) (h1 : term7 A B x x' y y') : y' = y.
Proof. exact (EQ_MP (@lem47994 A B x x' y y' h1) (@lem47990 A B x x' y y' h1)). Qed.
Lemma lem47996 {A B : Type'} (x : A) (y : B) (y' : B) (h1 : term30 A B x y y') : y' = y.
Proof. exact (ex_elim (@lem47927 A B x y y' h1) (fun x' : A => fun h0 : term29 A B x y y' x' => @lem47995 A B x x' y y' h0)). Qed.
Lemma lem47997 {A B : Type'} (x : A) (y' : B) (y : B) : term37 A B x y' y.
Proof. exact (fun h0 : term30 A B x y y' => @lem47996 A B x y y' h0). Qed.
Lemma lem47998 {A B : Type'} (x : A) (y : B) (y' : B) : term38 A B x y y'.
Proof. exact (conj (@lem47997 A B x y' y) (@lem47989 A B x y y')). Qed.
Lemma lem47999 {A B : Type'} (x : A) (y' : B) (y : B) : (term38 A B x y y') = ((term30 A B x y y') = (y' = y)).
Proof. exact (@lem32 (term30 A B x y y') (y' = y)). Qed.
Lemma lem48000 {A B : Type'} (x : A) (y' : B) (y : B) : (term30 A B x y y') = (y' = y).
Proof. exact (EQ_MP (@lem47999 A B x y' y) (@lem47998 A B x y y')). Qed.
Lemma lem48001 {A B : Type'} (x : A) (y' : B) (y : B) : (term25 A B x y y') = (y' = y).
Proof. exact (EQ_MP (@lem47926 A B x y' y) (@lem48000 A B x y' y)). Qed.
Lemma lem48002 {A B : Type'} (x : A) (y' : B) (y : B) : (term24 A B x y y') = (y' = y).
Proof. exact (EQ_MP (@lem47894 A B x y' y) (@lem48001 A B x y' y)). Qed.
Lemma lem48007 {A B : Type'} (x : A) (y : B) : term39 A B x y.
Proof. exact (fun y' : B => @lem48002 A B x y' y). Qed.
Lemma lem48008 {A B : Type'} (x : A) (y : B) : (term19 A B x y) = y.
Proof. exact (@lem47888 A B x y (@lem48007 A B x y)). Qed.
Lemma lem48009 {A B : Type'} (x : A) (y : B) : (term18 A B x y) = y.
Proof. exact (EQ_MP (@lem47884 A B x y) (@lem48008 A B x y)). Qed.
Lemma lem48014 {A B : Type'} (x : A) : term40 A B x.
Proof. exact (fun y : B => @lem48009 A B x y). Qed.
Lemma lem48019 {A B : Type'} : term41 A B.
Proof. exact (fun x : A => @lem48014 A B x). Qed.
