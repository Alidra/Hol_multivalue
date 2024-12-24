Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SING_GSPEC_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3399856 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3399857 {_88341 : Type'} (s : _88341 -> Prop) (t : _88341 -> Prop) : (s = t) = (term0 _88341 s t).
Proof. exact (@lem3399856 _88341 s t). Qed.
Lemma lem3399858 {_88341 : Type'} (a : _88341) : ((term1 _88341 a) = (@INSERT _88341 a (@EMPTY _88341))) = (term2 _88341 a).
Proof. exact (@lem3399857 _88341 (term1 _88341 a) (@INSERT _88341 a (@EMPTY _88341))). Qed.
Lemma lem3399875 {_88341 : Type'} : (term3 _88341) = (term4 _88341).
Proof. exact (fun_ext (fun a : _88341 => @lem3399858 _88341 a)). Qed.
Lemma lem3399876 {_88341 : Type'} : (@all _88341) = (@all _88341).
Proof. exact (eq_refl (@all _88341)). Qed.
Lemma lem3399877 {_88341 : Type'} : (term5 _88341) = (term6 _88341).
Proof. exact (MK_COMB (@lem3399876 _88341) (@lem3399875 _88341)). Qed.
Lemma lem3399882 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3399883 {_88341 : Type'} : (term7 _88341) = (term8 _88341).
Proof. exact (MK_COMB (@lem3399882) (@lem3399877 _88341)). Qed.
Lemma lem3399891 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3399892 {_88367 : Type'} (s : _88367 -> Prop) (t : _88367 -> Prop) : (s = t) = (term0 _88367 s t).
Proof. exact (@lem3399891 _88367 s t). Qed.
Lemma lem3399893 {_88367 : Type'} (a : _88367) : ((term9 _88367 a) = (@INSERT _88367 a (@EMPTY _88367))) = (term10 _88367 a).
Proof. exact (@lem3399892 _88367 (term9 _88367 a) (@INSERT _88367 a (@EMPTY _88367))). Qed.
Lemma lem3399910 {_88367 : Type'} : (term11 _88367) = (term12 _88367).
Proof. exact (fun_ext (fun a : _88367 => @lem3399893 _88367 a)). Qed.
Lemma lem3399911 {_88367 : Type'} : (@all _88367) = (@all _88367).
Proof. exact (eq_refl (@all _88367)). Qed.
Lemma lem3399912 {_88367 : Type'} : (term13 _88367) = (term14 _88367).
Proof. exact (MK_COMB (@lem3399911 _88367) (@lem3399910 _88367)). Qed.
Lemma lem3399917 {_88341 _88367 : Type'} : (term15 _88341 _88367) = (term16 _88341 _88367).
Proof. exact (MK_COMB (@lem3399883 _88341) (@lem3399912 _88367)). Qed.
Lemma lem3399920 {_88341 _88367 : Type'} : (term16 _88341 _88367) = (term15 _88341 _88367).
Proof. exact (SYM (@lem3399917 _88341 _88367)). Qed.
Lemma lem3399934 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term17 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3399935 {_88341 : Type'} (p : _88341 -> Prop) (x : _88341) : (term17 _88341 x p) = (p x).
Proof. exact (@lem3399934 _88341 p x). Qed.
Lemma lem3399936 {_88341 : Type'} (a : _88341) (x : _88341) : (term18 _88341 x a) = (term19 _88341 a x).
Proof. exact (@lem3399935 _88341 (term20 _88341 a) x). Qed.
Lemma lem3399937 {_88341 : Type'} (x : _88341) (a : _88341) : (term19 _88341 a x) = (x = a).
Proof. exact (eq_refl (term19 _88341 a x)). Qed.
Lemma lem3399938 {_88341 : Type'} (GEN_PVAR_28 : _88341) : (@SETSPEC _88341 GEN_PVAR_28) = (@SETSPEC _88341 GEN_PVAR_28).
Proof. exact (eq_refl (@SETSPEC _88341 GEN_PVAR_28)). Qed.
Lemma lem3399939 {_88341 : Type'} (GEN_PVAR_28 : _88341) (x : _88341) (a : _88341) : (term21 _88341 GEN_PVAR_28 a x) = (term22 _88341 GEN_PVAR_28 x a).
Proof. exact (MK_COMB (@lem3399938 _88341 GEN_PVAR_28) (@lem3399937 _88341 x a)). Qed.
Lemma lem3399940 {_88341 : Type'} (x : _88341) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3399941 {_88341 : Type'} (GEN_PVAR_28 : _88341) (a : _88341) (x : _88341) : (term23 _88341 GEN_PVAR_28 a x) = (term24 _88341 GEN_PVAR_28 a x).
Proof. exact (MK_COMB (@lem3399939 _88341 GEN_PVAR_28 x a) (@lem3399940 _88341 x)). Qed.
Lemma lem3399942 {_88341 : Type'} (GEN_PVAR_28 : _88341) (a : _88341) : (term25 _88341 GEN_PVAR_28 a) = (term26 _88341 GEN_PVAR_28 a).
Proof. exact (fun_ext (fun x : _88341 => @lem3399941 _88341 GEN_PVAR_28 a x)). Qed.
Lemma lem3399943 {_88341 : Type'} : (@ex _88341) = (@ex _88341).
Proof. exact (eq_refl (@ex _88341)). Qed.
Lemma lem3399944 {_88341 : Type'} (GEN_PVAR_28 : _88341) (a : _88341) : (term27 _88341 GEN_PVAR_28 a) = (term28 _88341 GEN_PVAR_28 a).
Proof. exact (MK_COMB (@lem3399943 _88341) (@lem3399942 _88341 GEN_PVAR_28 a)). Qed.
Lemma lem3399945 {_88341 : Type'} (a : _88341) : (term29 _88341 a) = (term30 _88341 a).
Proof. exact (fun_ext (fun GEN_PVAR_28 : _88341 => @lem3399944 _88341 GEN_PVAR_28 a)). Qed.
Lemma lem3399946 {_88341 : Type'} : (@GSPEC _88341) = (@GSPEC _88341).
Proof. exact (eq_refl (@GSPEC _88341)). Qed.
Lemma lem3399947 {_88341 : Type'} (a : _88341) : (term31 _88341 a) = (term1 _88341 a).
Proof. exact (MK_COMB (@lem3399946 _88341) (@lem3399945 _88341 a)). Qed.
Lemma lem3399948 {_88341 : Type'} (x : _88341) : (@IN _88341 x) = (@IN _88341 x).
Proof. exact (eq_refl (@IN _88341 x)). Qed.
Lemma lem3399949 {_88341 : Type'} (x : _88341) (a : _88341) : (term18 _88341 x a) = (term32 _88341 x a).
Proof. exact (MK_COMB (@lem3399948 _88341 x) (@lem3399947 _88341 a)). Qed.
Lemma lem3399950 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3399951 {_88341 : Type'} (x : _88341) (a : _88341) : (term33 _88341 x a) = (term34 _88341 x a).
Proof. exact (MK_COMB (@lem3399950) (@lem3399949 _88341 x a)). Qed.
Lemma lem3399952 {_88341 : Type'} (x : _88341) (a : _88341) : (term19 _88341 a x) = (x = a).
Proof. exact (eq_refl (term19 _88341 a x)). Qed.
Lemma lem3399953 {_88341 : Type'} (x : _88341) (a : _88341) : ((term18 _88341 x a) = (term19 _88341 a x)) = ((term32 _88341 x a) = (x = a)).
Proof. exact (MK_COMB (@lem3399951 _88341 x a) (@lem3399952 _88341 x a)). Qed.
Lemma lem3399954 {_88341 : Type'} (x : _88341) (a : _88341) : (term32 _88341 x a) = (x = a).
Proof. exact (EQ_MP (@lem3399953 _88341 x a) (@lem3399936 _88341 a x)). Qed.
Lemma lem3399957 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3399958 {_88341 : Type'} (x : _88341) (a : _88341) : (term34 _88341 x a) = (term35 _88341 x a).
Proof. exact (MK_COMB (@lem3399957) (@lem3399954 _88341 x a)). Qed.
Lemma lem3399960 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term36 A x y s) = (term37 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3399961 {_88341 : Type'} (y : _88341) (x : _88341) (s : _88341 -> Prop) : (term36 _88341 x y s) = (term37 _88341 y x s).
Proof. exact (@lem3399960 _88341 y x s). Qed.
Lemma lem3399962 {_88341 : Type'} (a : _88341) (x : _88341) : (term38 _88341 x a) = (term39 _88341 a x).
Proof. exact (@lem3399961 _88341 a x (@EMPTY _88341)). Qed.
Lemma lem3399968 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3399969 {_88341 : Type'} (x : _88341) : (@IN _88341 x (@EMPTY _88341)) = False.
Proof. exact (@lem3399968 _88341 x). Qed.
Lemma lem3399970 {_88341 : Type'} (x : _88341) (a : _88341) : (term40 _88341 x a) = (term40 _88341 x a).
Proof. exact (eq_refl (term40 _88341 x a)). Qed.
Lemma lem3399971 {_88341 : Type'} (x : _88341) (a : _88341) : (term39 _88341 a x) = (term41 _88341 x a).
Proof. exact (MK_COMB (@lem3399970 _88341 x a) (@lem3399969 _88341 x)). Qed.
Lemma lem3399973 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem3399974 {_88341 : Type'} (x : _88341) (a : _88341) : (term41 _88341 x a) = (x = a).
Proof. exact (@lem3399973 (x = a)). Qed.
Lemma lem3399977 {_88341 : Type'} (x : _88341) (a : _88341) : (term39 _88341 a x) = (x = a).
Proof. exact (TRANS (@lem3399971 _88341 x a) (@lem3399974 _88341 x a)). Qed.
Lemma lem3399978 {_88341 : Type'} (x : _88341) (a : _88341) : (term38 _88341 x a) = (x = a).
Proof. exact (TRANS (@lem3399962 _88341 a x) (@lem3399977 _88341 x a)). Qed.
Lemma lem3399979 {_88341 : Type'} (x : _88341) (a : _88341) : ((term32 _88341 x a) = (term38 _88341 x a)) = ((x = a) = (x = a)).
Proof. exact (MK_COMB (@lem3399958 _88341 x a) (@lem3399978 _88341 x a)). Qed.
Lemma lem3399981 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3399982 (x : Prop) : (x = x) = True.
Proof. exact (@lem3399981 Prop x). Qed.
Lemma lem3399983 {_88341 : Type'} (x : _88341) (a : _88341) : ((x = a) = (x = a)) = True.
Proof. exact (@lem3399982 (x = a)). Qed.
Lemma lem3399984 {_88341 : Type'} (x : _88341) (a : _88341) : ((term32 _88341 x a) = (term38 _88341 x a)) = True.
Proof. exact (TRANS (@lem3399979 _88341 x a) (@lem3399983 _88341 x a)). Qed.
Lemma lem3399985 {_88341 : Type'} (a : _88341) : (term42 _88341 a) = (term43 _88341).
Proof. exact (fun_ext (fun x : _88341 => @lem3399984 _88341 x a)). Qed.
Lemma lem3399986 {_88341 : Type'} : (@all _88341) = (@all _88341).
Proof. exact (eq_refl (@all _88341)). Qed.
Lemma lem3399987 {_88341 : Type'} (a : _88341) : (term2 _88341 a) = (term44 _88341).
Proof. exact (MK_COMB (@lem3399986 _88341) (@lem3399985 _88341 a)). Qed.
Lemma lem3399989 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3399990 {_88341 : Type'} (t : Prop) : (term45 _88341 t) = t.
Proof. exact (@lem3399989 _88341 t). Qed.
Lemma lem3399991 {_88341 : Type'} : (term44 _88341) = True.
Proof. exact (@lem3399990 _88341 True). Qed.
Lemma lem3399992 {_88341 : Type'} (a : _88341) : (term2 _88341 a) = True.
Proof. exact (TRANS (@lem3399987 _88341 a) (@lem3399991 _88341)). Qed.
Lemma lem3399993 {_88341 : Type'} : (term4 _88341) = (term43 _88341).
Proof. exact (fun_ext (fun a : _88341 => @lem3399992 _88341 a)). Qed.
Lemma lem3399994 {_88341 : Type'} : (@all _88341) = (@all _88341).
Proof. exact (eq_refl (@all _88341)). Qed.
Lemma lem3399995 {_88341 : Type'} : (term6 _88341) = (term44 _88341).
Proof. exact (MK_COMB (@lem3399994 _88341) (@lem3399993 _88341)). Qed.
Lemma lem3399997 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3399998 {_88341 : Type'} (t : Prop) : (term45 _88341 t) = t.
Proof. exact (@lem3399997 _88341 t). Qed.
Lemma lem3399999 {_88341 : Type'} : (term44 _88341) = True.
Proof. exact (@lem3399998 _88341 True). Qed.
Lemma lem3400000 {_88341 : Type'} : (term6 _88341) = True.
Proof. exact (TRANS (@lem3399995 _88341) (@lem3399999 _88341)). Qed.
Lemma lem3400001 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3400002 {_88341 : Type'} : (term8 _88341) = (and True).
Proof. exact (MK_COMB (@lem3400001) (@lem3400000 _88341)). Qed.
Lemma lem3400014 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term17 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3400015 {_88367 : Type'} (p : _88367 -> Prop) (x : _88367) : (term17 _88367 x p) = (p x).
Proof. exact (@lem3400014 _88367 p x). Qed.
Lemma lem3400016 {_88367 : Type'} (a : _88367) (x : _88367) : (term46 _88367 x a) = (term47 _88367 a x).
Proof. exact (@lem3400015 _88367 (term48 _88367 a) x). Qed.
Lemma lem3400017 {_88367 : Type'} (a : _88367) (x : _88367) : (term47 _88367 a x) = (a = x).
Proof. exact (eq_refl (term47 _88367 a x)). Qed.
Lemma lem3400018 {_88367 : Type'} (GEN_PVAR_29 : _88367) : (@SETSPEC _88367 GEN_PVAR_29) = (@SETSPEC _88367 GEN_PVAR_29).
Proof. exact (eq_refl (@SETSPEC _88367 GEN_PVAR_29)). Qed.
Lemma lem3400019 {_88367 : Type'} (GEN_PVAR_29 : _88367) (a : _88367) (x : _88367) : (term49 _88367 GEN_PVAR_29 a x) = (term22 _88367 GEN_PVAR_29 a x).
Proof. exact (MK_COMB (@lem3400018 _88367 GEN_PVAR_29) (@lem3400017 _88367 a x)). Qed.
Lemma lem3400020 {_88367 : Type'} (x : _88367) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3400021 {_88367 : Type'} (GEN_PVAR_29 : _88367) (a : _88367) (x : _88367) : (term50 _88367 GEN_PVAR_29 a x) = (term51 _88367 GEN_PVAR_29 a x).
Proof. exact (MK_COMB (@lem3400019 _88367 GEN_PVAR_29 a x) (@lem3400020 _88367 x)). Qed.
Lemma lem3400022 {_88367 : Type'} (GEN_PVAR_29 : _88367) (a : _88367) : (term52 _88367 GEN_PVAR_29 a) = (term53 _88367 GEN_PVAR_29 a).
Proof. exact (fun_ext (fun x : _88367 => @lem3400021 _88367 GEN_PVAR_29 a x)). Qed.
Lemma lem3400023 {_88367 : Type'} : (@ex _88367) = (@ex _88367).
Proof. exact (eq_refl (@ex _88367)). Qed.
Lemma lem3400024 {_88367 : Type'} (GEN_PVAR_29 : _88367) (a : _88367) : (term54 _88367 GEN_PVAR_29 a) = (term55 _88367 GEN_PVAR_29 a).
Proof. exact (MK_COMB (@lem3400023 _88367) (@lem3400022 _88367 GEN_PVAR_29 a)). Qed.
Lemma lem3400025 {_88367 : Type'} (a : _88367) : (term56 _88367 a) = (term57 _88367 a).
Proof. exact (fun_ext (fun GEN_PVAR_29 : _88367 => @lem3400024 _88367 GEN_PVAR_29 a)). Qed.
Lemma lem3400026 {_88367 : Type'} : (@GSPEC _88367) = (@GSPEC _88367).
Proof. exact (eq_refl (@GSPEC _88367)). Qed.
Lemma lem3400027 {_88367 : Type'} (a : _88367) : (term58 _88367 a) = (term9 _88367 a).
Proof. exact (MK_COMB (@lem3400026 _88367) (@lem3400025 _88367 a)). Qed.
Lemma lem3400028 {_88367 : Type'} (x : _88367) : (@IN _88367 x) = (@IN _88367 x).
Proof. exact (eq_refl (@IN _88367 x)). Qed.
Lemma lem3400029 {_88367 : Type'} (x : _88367) (a : _88367) : (term46 _88367 x a) = (term59 _88367 x a).
Proof. exact (MK_COMB (@lem3400028 _88367 x) (@lem3400027 _88367 a)). Qed.
Lemma lem3400030 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3400031 {_88367 : Type'} (x : _88367) (a : _88367) : (term60 _88367 x a) = (term61 _88367 x a).
Proof. exact (MK_COMB (@lem3400030) (@lem3400029 _88367 x a)). Qed.
Lemma lem3400032 {_88367 : Type'} (a : _88367) (x : _88367) : (term47 _88367 a x) = (a = x).
Proof. exact (eq_refl (term47 _88367 a x)). Qed.
Lemma lem3400033 {_88367 : Type'} (a : _88367) (x : _88367) : ((term46 _88367 x a) = (term47 _88367 a x)) = ((term59 _88367 x a) = (a = x)).
Proof. exact (MK_COMB (@lem3400031 _88367 x a) (@lem3400032 _88367 a x)). Qed.
Lemma lem3400034 {_88367 : Type'} (a : _88367) (x : _88367) : (term59 _88367 x a) = (a = x).
Proof. exact (EQ_MP (@lem3400033 _88367 a x) (@lem3400016 _88367 a x)). Qed.
Lemma lem3400037 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3400038 {_88367 : Type'} (a : _88367) (x : _88367) : (term61 _88367 x a) = (term35 _88367 a x).
Proof. exact (MK_COMB (@lem3400037) (@lem3400034 _88367 a x)). Qed.
Lemma lem3400040 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term36 A x y s) = (term37 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3400041 {_88367 : Type'} (y : _88367) (x : _88367) (s : _88367 -> Prop) : (term36 _88367 x y s) = (term37 _88367 y x s).
Proof. exact (@lem3400040 _88367 y x s). Qed.
Lemma lem3400042 {_88367 : Type'} (a : _88367) (x : _88367) : (term38 _88367 x a) = (term39 _88367 a x).
Proof. exact (@lem3400041 _88367 a x (@EMPTY _88367)). Qed.
Lemma lem3400048 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3400049 {_88367 : Type'} (x : _88367) : (@IN _88367 x (@EMPTY _88367)) = False.
Proof. exact (@lem3400048 _88367 x). Qed.
Lemma lem3400050 {_88367 : Type'} (x : _88367) (a : _88367) : (term40 _88367 x a) = (term40 _88367 x a).
Proof. exact (eq_refl (term40 _88367 x a)). Qed.
Lemma lem3400051 {_88367 : Type'} (x : _88367) (a : _88367) : (term39 _88367 a x) = (term41 _88367 x a).
Proof. exact (MK_COMB (@lem3400050 _88367 x a) (@lem3400049 _88367 x)). Qed.
Lemma lem3400053 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem3400054 {_88367 : Type'} (x : _88367) (a : _88367) : (term41 _88367 x a) = (x = a).
Proof. exact (@lem3400053 (x = a)). Qed.
Lemma lem3400057 {_88367 : Type'} (x : _88367) (a : _88367) : (term39 _88367 a x) = (x = a).
Proof. exact (TRANS (@lem3400051 _88367 x a) (@lem3400054 _88367 x a)). Qed.
Lemma lem3400058 {_88367 : Type'} (x : _88367) (a : _88367) : (term38 _88367 x a) = (x = a).
Proof. exact (TRANS (@lem3400042 _88367 a x) (@lem3400057 _88367 x a)). Qed.
Lemma lem3400059 {_88367 : Type'} (x : _88367) (a : _88367) : ((term59 _88367 x a) = (term38 _88367 x a)) = ((a = x) = (x = a)).
Proof. exact (MK_COMB (@lem3400038 _88367 a x) (@lem3400058 _88367 x a)). Qed.
Lemma lem3400062 {_88367 : Type'} (a : _88367) : (term62 _88367 a) = (term63 _88367 a).
Proof. exact (fun_ext (fun x : _88367 => @lem3400059 _88367 x a)). Qed.
Lemma lem3400063 {_88367 : Type'} : (@all _88367) = (@all _88367).
Proof. exact (eq_refl (@all _88367)). Qed.
Lemma lem3400064 {_88367 : Type'} (a : _88367) : (term10 _88367 a) = (term64 _88367 a).
Proof. exact (MK_COMB (@lem3400063 _88367) (@lem3400062 _88367 a)). Qed.
Lemma lem3400069 {_88367 : Type'} : (term12 _88367) = (term65 _88367).
Proof. exact (fun_ext (fun a : _88367 => @lem3400064 _88367 a)). Qed.
Lemma lem3400070 {_88367 : Type'} : (@all _88367) = (@all _88367).
Proof. exact (eq_refl (@all _88367)). Qed.
Lemma lem3400071 {_88367 : Type'} : (term14 _88367) = (term66 _88367).
Proof. exact (MK_COMB (@lem3400070 _88367) (@lem3400069 _88367)). Qed.
Lemma lem3400076 {_88341 _88367 : Type'} : (term16 _88341 _88367) = (term67 _88367).
Proof. exact (MK_COMB (@lem3400002 _88341) (@lem3400071 _88367)). Qed.
Lemma lem3400078 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3400079 {_88367 : Type'} : (term67 _88367) = (term66 _88367).
Proof. exact (@lem3400078 (term66 _88367)). Qed.
Lemma lem3400094 {_88341 _88367 : Type'} : (term16 _88341 _88367) = (term66 _88367).
Proof. exact (TRANS (@lem3400076 _88341 _88367) (@lem3400079 _88367)). Qed.
Lemma lem3400095 {_88341 _88367 : Type'} : (term66 _88367) = (term16 _88341 _88367).
Proof. exact (SYM (@lem3400094 _88341 _88367)). Qed.
Lemma lem3400097 (p : Prop) : p = (term68 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3400098 {_88367 : Type'} : (term66 _88367) = (term69 _88367).
Proof. exact (@lem3400097 (term66 _88367)). Qed.
Lemma lem3400099 {_88367 : Type'} : (term69 _88367) = (term66 _88367).
Proof. exact (SYM (@lem3400098 _88367)). Qed.
Lemma lem3400100 {_88367 : Type'} (h1 : term70 _88367) : term70 _88367.
Proof. exact (h1). Qed.
Lemma lem3400103 {_88367 : Type'} (h1 : term69 _88367) : term69 _88367.
Proof. exact (h1). Qed.
Lemma lem3400104 {_88367 : Type'} : term71 _88367.
Proof. exact (fun h0 : term69 _88367 => @lem3400103 _88367 h0). Qed.
Lemma lem3400105 {_88367 : Type'} (h1 : term71 _88367) : term71 _88367.
Proof. exact (h1). Qed.
Lemma lem3400106 {_88367 : Type'} (h1 : term69 _88367) : term69 _88367.
Proof. exact (h1). Qed.
Lemma lem3400107 {_88367 : Type'} (h1 : term69 _88367) (h2 : term71 _88367) : term69 _88367.
Proof. exact (@lem3400105 _88367 h2 (@lem3400106 _88367 h1)). Qed.
Lemma lem3400108 {_88367 : Type'} (h1 : term69 _88367) : term72 _88367.
Proof. exact (fun h0 : term71 _88367 => @lem3400107 _88367 h1 h0). Qed.
Lemma lem3400109 {_88367 : Type'} (h1 : term71 _88367) : term71 _88367.
Proof. exact (h1). Qed.
Lemma lem3400110 {_88367 : Type'} (h1 : term69 _88367) (h2 : term71 _88367) : term69 _88367.
Proof. exact (@lem3400108 _88367 h1 (@lem3400109 _88367 h2)). Qed.
Lemma lem3400111 {_88367 : Type'} (h1 : term71 _88367) : term71 _88367.
Proof. exact (fun h0 : term69 _88367 => @lem3400110 _88367 h0 h1). Qed.
Lemma lem3400112 {_88367 : Type'} : term73 _88367.
Proof. exact (fun h0 : term71 _88367 => @lem3400111 _88367 h0). Qed.
Lemma lem3400115 {_88367 : Type'} : term71 _88367.
Proof. exact (@lem3400112 _88367 (@lem3400104 _88367)). Qed.
Lemma lem3400116 {_88367 : Type'} : term71 _88367.
Proof. exact (@lem3400115 _88367). Qed.
Lemma lem3400118 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3400119 {_88367 : Type'} : (term69 _88367) = (term74 _88367).
Proof. exact (@lem3400118 (term70 _88367)). Qed.
Lemma lem3400121 (t : Prop) : (term75 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3400122 {_88367 : Type'} : (term74 _88367) = (term66 _88367).
Proof. exact (@lem3400121 (term66 _88367)). Qed.
Lemma lem3400135 {_88367 : Type'} : (term69 _88367) = (term66 _88367).
Proof. exact (TRANS (@lem3400119 _88367) (@lem3400122 _88367)). Qed.
Lemma lem3400140 {_88367 : Type'} (x : _88367) (a : _88367) : ((a = x) = (x = a)) = ((a = x) = (x = a)).
Proof. exact (eq_refl ((a = x) = (x = a))). Qed.
Lemma lem3400141 {_88367 : Type'} (a : _88367) : (term63 _88367 a) = (term63 _88367 a).
Proof. exact (fun_ext (fun x : _88367 => @lem3400140 _88367 x a)). Qed.
Lemma lem3400142 {_88367 : Type'} : (@all _88367) = (@all _88367).
Proof. exact (eq_refl (@all _88367)). Qed.
Lemma lem3400143 {_88367 : Type'} (a : _88367) : (term64 _88367 a) = (term64 _88367 a).
Proof. exact (MK_COMB (@lem3400142 _88367) (@lem3400141 _88367 a)). Qed.
Lemma lem3400144 {_88367 : Type'} : (term65 _88367) = (term65 _88367).
Proof. exact (fun_ext (fun a : _88367 => @lem3400143 _88367 a)). Qed.
Lemma lem3400145 {_88367 : Type'} : (@all _88367) = (@all _88367).
Proof. exact (eq_refl (@all _88367)). Qed.
Lemma lem3400146 {_88367 : Type'} : (term66 _88367) = (term66 _88367).
Proof. exact (MK_COMB (@lem3400145 _88367) (@lem3400144 _88367)). Qed.
Lemma lem3400161 {_88367 : Type'} : (term69 _88367) = (term66 _88367).
Proof. exact (TRANS (@lem3400135 _88367) (@lem3400146 _88367)). Qed.
Lemma lem3400162 {_88367 : Type'} : (term66 _88367) = (term69 _88367).
Proof. exact (SYM (@lem3400161 _88367)). Qed.
Lemma lem3400164 (p : Prop) : p = (term68 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3400165 {_88367 : Type'} (x : _88367) (a : _88367) : ((a = x) = (x = a)) = (term76 _88367 x a).
Proof. exact (@lem3400164 ((a = x) = (x = a))). Qed.
Lemma lem3400166 {_88367 : Type'} (x : _88367) (a : _88367) : (term76 _88367 x a) = ((a = x) = (x = a)).
Proof. exact (SYM (@lem3400165 _88367 x a)). Qed.
Lemma lem3400167 {_88367 : Type'} (x : _88367) (a : _88367) (h1 : term77 _88367 x a) : term77 _88367 x a.
Proof. exact (h1). Qed.
Lemma lem3400186 {_88367 : Type'} (x : _88367) (a : _88367) : (term77 _88367 x a) = (term78 _88367 x a).
Proof. exact (@lem17646 (a = x) (x = a)). Qed.
Lemma lem3400221 {_88367 : Type'} (x : _88367) (a : _88367) (h1 : term77 _88367 x a) : term78 _88367 x a.
Proof. exact (EQ_MP (@lem3400186 _88367 x a) (@lem3400167 _88367 x a h1)). Qed.
Lemma lem3400222 {_88367 : Type'} (x : _88367) (a : _88367) (h1 : term79 _88367 x a) : term79 _88367 x a.
Proof. exact (h1). Qed.
Lemma lem3400223 {_88367 : Type'} (x : _88367) (a : _88367) (h1 : term80 _88367 x a) : term80 _88367 x a.
Proof. exact (h1). Qed.
Lemma lem3400245 {_88367 : Type'} (x : _88367) (a : _88367) (h1 : term79 _88367 x a) : a = x.
Proof. exact (proj1 (@lem3400222 _88367 x a h1)). Qed.
Lemma lem3400247 {_88367 : Type'} (x : _88367) (a : _88367) (h1 : term79 _88367 x a) : term81 _88367 x a.
Proof. exact (proj2 (@lem3400222 _88367 x a h1)). Qed.
Lemma lem3400249 {_88367 : Type'} (x : _88367) (a : _88367) (h1 : term80 _88367 x a) : term81 _88367 a x.
Proof. exact (proj1 (@lem3400223 _88367 x a h1)). Qed.
Lemma lem3400251 {_88367 : Type'} (x : _88367) (a : _88367) (h1 : term80 _88367 x a) : x = a.
Proof. exact (proj2 (@lem3400223 _88367 x a h1)). Qed.
Lemma lem3400266 {_88367 : Type'} (x : _88367) : (term82 _88367 x) = (term82 _88367 x).
Proof. exact (eq_refl (term82 _88367 x)). Qed.
Lemma lem3400267 {_88367 : Type'} (x : _88367) (a : _88367) (h1 : term79 _88367 x a) : (term83 _88367 x a) = (term84 _88367 x).
Proof. exact (MK_COMB (@lem3400266 _88367 x) (@lem3400245 _88367 x a h1)). Qed.
Lemma lem3400268 {_88367 : Type'} (x : _88367) : (term84 _88367 x) = (term85 _88367 x).
Proof. exact (eq_refl (term84 _88367 x)). Qed.
Lemma lem3400269 {_88367 : Type'} (x : _88367) (a : _88367) : (term86 _88367 x a) = (term86 _88367 x a).
Proof. exact (eq_refl (term86 _88367 x a)). Qed.
Lemma lem3400270 {_88367 : Type'} (a : _88367) (x : _88367) : ((term83 _88367 x a) = (term84 _88367 x)) = ((term83 _88367 x a) = (term85 _88367 x)).
Proof. exact (MK_COMB (@lem3400269 _88367 x a) (@lem3400268 _88367 x)). Qed.
Lemma lem3400271 {_88367 : Type'} (x : _88367) (a : _88367) : (term83 _88367 x a) = (term81 _88367 x a).
Proof. exact (eq_refl (term83 _88367 x a)). Qed.
Lemma lem3400272 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3400273 {_88367 : Type'} (x : _88367) (a : _88367) : (term86 _88367 x a) = (term87 _88367 x a).
Proof. exact (MK_COMB (@lem3400272) (@lem3400271 _88367 x a)). Qed.
Lemma lem3400274 {_88367 : Type'} (x : _88367) : (term85 _88367 x) = (term85 _88367 x).
Proof. exact (eq_refl (term85 _88367 x)). Qed.
Lemma lem3400275 {_88367 : Type'} (a : _88367) (x : _88367) : ((term83 _88367 x a) = (term85 _88367 x)) = ((term81 _88367 x a) = (term85 _88367 x)).
Proof. exact (MK_COMB (@lem3400273 _88367 x a) (@lem3400274 _88367 x)). Qed.
Lemma lem3400276 {_88367 : Type'} (a : _88367) (x : _88367) : ((term83 _88367 x a) = (term84 _88367 x)) = ((term81 _88367 x a) = (term85 _88367 x)).
Proof. exact (TRANS (@lem3400270 _88367 a x) (@lem3400275 _88367 a x)). Qed.
Lemma lem3400277 {_88367 : Type'} (x : _88367) (a : _88367) (h1 : term79 _88367 x a) : (term81 _88367 x a) = (term85 _88367 x).
Proof. exact (EQ_MP (@lem3400276 _88367 a x) (@lem3400267 _88367 x a h1)). Qed.
Lemma lem3400278 {_88367 : Type'} (x : _88367) (a : _88367) (h1 : term79 _88367 x a) : term85 _88367 x.
Proof. exact (EQ_MP (@lem3400277 _88367 x a h1) (@lem3400247 _88367 x a h1)). Qed.
Lemma lem3400293 {_88367 : Type'} (a : _88367) : (term82 _88367 a) = (term82 _88367 a).
Proof. exact (eq_refl (term82 _88367 a)). Qed.
Lemma lem3400294 {_88367 : Type'} (x : _88367) (a : _88367) (h1 : term80 _88367 x a) : (term83 _88367 a x) = (term84 _88367 a).
Proof. exact (MK_COMB (@lem3400293 _88367 a) (@lem3400251 _88367 x a h1)). Qed.
Lemma lem3400295 {_88367 : Type'} (a : _88367) : (term84 _88367 a) = (term85 _88367 a).
Proof. exact (eq_refl (term84 _88367 a)). Qed.
Lemma lem3400296 {_88367 : Type'} (a : _88367) (x : _88367) : (term86 _88367 a x) = (term86 _88367 a x).
Proof. exact (eq_refl (term86 _88367 a x)). Qed.
Lemma lem3400297 {_88367 : Type'} (x : _88367) (a : _88367) : ((term83 _88367 a x) = (term84 _88367 a)) = ((term83 _88367 a x) = (term85 _88367 a)).
Proof. exact (MK_COMB (@lem3400296 _88367 a x) (@lem3400295 _88367 a)). Qed.
Lemma lem3400298 {_88367 : Type'} (a : _88367) (x : _88367) : (term83 _88367 a x) = (term81 _88367 a x).
Proof. exact (eq_refl (term83 _88367 a x)). Qed.
Lemma lem3400299 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3400300 {_88367 : Type'} (a : _88367) (x : _88367) : (term86 _88367 a x) = (term87 _88367 a x).
Proof. exact (MK_COMB (@lem3400299) (@lem3400298 _88367 a x)). Qed.
Lemma lem3400301 {_88367 : Type'} (a : _88367) : (term85 _88367 a) = (term85 _88367 a).
Proof. exact (eq_refl (term85 _88367 a)). Qed.
Lemma lem3400302 {_88367 : Type'} (x : _88367) (a : _88367) : ((term83 _88367 a x) = (term85 _88367 a)) = ((term81 _88367 a x) = (term85 _88367 a)).
Proof. exact (MK_COMB (@lem3400300 _88367 a x) (@lem3400301 _88367 a)). Qed.
Lemma lem3400303 {_88367 : Type'} (x : _88367) (a : _88367) : ((term83 _88367 a x) = (term84 _88367 a)) = ((term81 _88367 a x) = (term85 _88367 a)).
Proof. exact (TRANS (@lem3400297 _88367 x a) (@lem3400302 _88367 x a)). Qed.
Lemma lem3400304 {_88367 : Type'} (x : _88367) (a : _88367) (h1 : term80 _88367 x a) : (term81 _88367 a x) = (term85 _88367 a).
Proof. exact (EQ_MP (@lem3400303 _88367 x a) (@lem3400294 _88367 x a h1)). Qed.
Lemma lem3400305 {_88367 : Type'} (x : _88367) (a : _88367) (h1 : term80 _88367 x a) : term85 _88367 a.
Proof. exact (EQ_MP (@lem3400304 _88367 x a h1) (@lem3400249 _88367 x a h1)). Qed.
Lemma lem3400309 {_88367 : Type'} (x : _88367) : x = x.
Proof. exact (@lem21386 _88367 x). Qed.
Lemma lem3400310 {_88367 : Type'} (x : _88367) : x = x.
Proof. exact (@lem3400309 _88367 x). Qed.
Lemma lem3400311 {_88367 : Type'} (x : _88367) : term88 _88367 x.
Proof. exact (fun h0 : term85 _88367 x => @lem3400310 _88367 x). Qed.
Lemma lem3400313 (p : Prop) : (term89 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3400314 {_88367 : Type'} (x : _88367) : (term88 _88367 x) = (x = x).
Proof. exact (@lem3400313 (x = x)). Qed.
Lemma lem3400315 {_88367 : Type'} (x : _88367) : x = x.
Proof. exact (EQ_MP (@lem3400314 _88367 x) (@lem3400311 _88367 x)). Qed.
Lemma lem3400318 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3400320 {_88367 : Type'} (x : _88367) : (term85 _88367 x) = (term90 _88367 x).
Proof. exact (@lem3400318 (x = x)). Qed.
Lemma lem3400323 {_88367 : Type'} (x : _88367) (a : _88367) (h1 : term79 _88367 x a) : term90 _88367 x.
Proof. exact (EQ_MP (@lem3400320 _88367 x) (@lem3400278 _88367 x a h1)). Qed.
Lemma lem3400326 {_88367 : Type'} (x : _88367) (a : _88367) (h1 : term79 _88367 x a) : False.
Proof. exact (@lem3400323 _88367 x a h1 (@lem3400315 _88367 x)). Qed.
Lemma lem3400327 {_88367 : Type'} (x : _88367) (a : _88367) (h1 : term79 _88367 x a) : term91.
Proof. exact (fun h0 : ~ False => @lem3400326 _88367 x a h1). Qed.
Lemma lem3400329 (p : Prop) : (term89 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3400330 : term91 = False.
Proof. exact (@lem3400329 False). Qed.
Lemma lem3400335 {_88367 : Type'} (x : _88367) : x = x.
Proof. exact (@lem21386 _88367 x). Qed.
Lemma lem3400336 {_88367 : Type'} (x : _88367) : x = x.
Proof. exact (@lem3400335 _88367 x). Qed.
Lemma lem3400337 {_88367 : Type'} (a : _88367) : a = a.
Proof. exact (@lem3400336 _88367 a). Qed.
Lemma lem3400338 {_88367 : Type'} (a : _88367) : term88 _88367 a.
Proof. exact (fun h0 : term85 _88367 a => @lem3400337 _88367 a). Qed.
Lemma lem3400340 (p : Prop) : (term89 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3400341 {_88367 : Type'} (a : _88367) : (term88 _88367 a) = (a = a).
Proof. exact (@lem3400340 (a = a)). Qed.
Lemma lem3400342 {_88367 : Type'} (a : _88367) : a = a.
Proof. exact (EQ_MP (@lem3400341 _88367 a) (@lem3400338 _88367 a)). Qed.
Lemma lem3400345 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3400347 {_88367 : Type'} (a : _88367) : (term85 _88367 a) = (term90 _88367 a).
Proof. exact (@lem3400345 (a = a)). Qed.
Lemma lem3400350 {_88367 : Type'} (x : _88367) (a : _88367) (h1 : term80 _88367 x a) : term90 _88367 a.
Proof. exact (EQ_MP (@lem3400347 _88367 a) (@lem3400305 _88367 x a h1)). Qed.
Lemma lem3400353 {_88367 : Type'} (x : _88367) (a : _88367) (h1 : term80 _88367 x a) : False.
Proof. exact (@lem3400350 _88367 x a h1 (@lem3400342 _88367 a)). Qed.
Lemma lem3400354 {_88367 : Type'} (x : _88367) (a : _88367) (h1 : term80 _88367 x a) : term91.
Proof. exact (fun h0 : ~ False => @lem3400353 _88367 x a h1). Qed.
Lemma lem3400356 (p : Prop) : (term89 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3400357 : term91 = False.
Proof. exact (@lem3400356 False). Qed.
Lemma lem3400359 {_88367 : Type'} (x : _88367) (a : _88367) (h1 : term80 _88367 x a) : False.
Proof. exact (EQ_MP (@lem3400357) (@lem3400354 _88367 x a h1)). Qed.
Lemma lem3400360 {_88367 : Type'} (x : _88367) (a : _88367) (h1 : term79 _88367 x a) : False.
Proof. exact (EQ_MP (@lem3400330) (@lem3400327 _88367 x a h1)). Qed.
Lemma lem3400361 {_88367 : Type'} (x : _88367) (a : _88367) (h1 : term77 _88367 x a) : False.
Proof. exact (or_elim (@lem3400221 _88367 x a h1) (fun h0 : term79 _88367 x a => @lem3400360 _88367 x a h0) (fun h0 : term80 _88367 x a => @lem3400359 _88367 x a h0)). Qed.
Lemma lem3400362 {_88367 : Type'} (x : _88367) (a : _88367) (h1 : term77 _88367 x a) : (term77 _88367 x a) = False.
Proof. exact (prop_ext (fun h2 : term77 _88367 x a => @lem3400361 _88367 x a h1) (fun h2 : False => @lem3400167 _88367 x a h1)). Qed.
Lemma lem3400363 {_88367 : Type'} (x : _88367) (a : _88367) (h1 : term77 _88367 x a) : False.
Proof. exact (EQ_MP (@lem3400362 _88367 x a h1) (@lem3400167 _88367 x a h1)). Qed.
Lemma lem3400364 {_88367 : Type'} (x : _88367) (a : _88367) : term76 _88367 x a.
Proof. exact (fun h0 : term77 _88367 x a => @lem3400363 _88367 x a h0). Qed.
Lemma lem3400365 {_88367 : Type'} (x : _88367) (a : _88367) : (a = x) = (x = a).
Proof. exact (EQ_MP (@lem3400166 _88367 x a) (@lem3400364 _88367 x a)). Qed.
Lemma lem3400370 {_88367 : Type'} (a : _88367) : term64 _88367 a.
Proof. exact (fun x : _88367 => @lem3400365 _88367 x a). Qed.
Lemma lem3400375 {_88367 : Type'} : term66 _88367.
Proof. exact (fun a : _88367 => @lem3400370 _88367 a). Qed.
Lemma lem3400376 {_88367 : Type'} : term69 _88367.
Proof. exact (EQ_MP (@lem3400162 _88367) (@lem3400375 _88367)). Qed.
Lemma lem3400378 {_88367 : Type'} : term69 _88367.
Proof. exact (@lem3400116 _88367 (@lem3400376 _88367)). Qed.
Lemma lem3400379 {_88367 : Type'} (h1 : term70 _88367) : False.
Proof. exact (@lem3400378 _88367 (@lem3400100 _88367 h1)). Qed.
Lemma lem3400380 {_88367 : Type'} (h1 : term70 _88367) : (term70 _88367) = False.
Proof. exact (prop_ext (fun h2 : term70 _88367 => @lem3400379 _88367 h1) (fun h2 : False => @lem3400100 _88367 h1)). Qed.
Lemma lem3400381 {_88367 : Type'} (h1 : term70 _88367) : False.
Proof. exact (EQ_MP (@lem3400380 _88367 h1) (@lem3400100 _88367 h1)). Qed.
Lemma lem3400382 {_88367 : Type'} : term69 _88367.
Proof. exact (fun h0 : term70 _88367 => @lem3400381 _88367 h0). Qed.
Lemma lem3400383 {_88367 : Type'} : term66 _88367.
Proof. exact (EQ_MP (@lem3400099 _88367) (@lem3400382 _88367)). Qed.
Lemma lem3400384 {_88341 _88367 : Type'} : term16 _88341 _88367.
Proof. exact (EQ_MP (@lem3400095 _88341 _88367) (@lem3400383 _88367)). Qed.
Lemma lem3400385 {_88341 _88367 : Type'} : term15 _88341 _88367.
Proof. exact (EQ_MP (@lem3399920 _88341 _88367) (@lem3400384 _88341 _88367)). Qed.
