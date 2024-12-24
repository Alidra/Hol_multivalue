Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3454059_term_abbrevs.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm3453886_spec.
Require Import thm3453887_spec.
Require Import thm3453893_spec.
Require Import thm3453894_spec.
Require Import thm3453899_spec.
Require Import thm3453900_spec.
Lemma lem3453930 {A : Type'} (s : type686 A) (x : A) : (term0 A x s) = (term1 A s x).
Proof. exact (EQ_MP (@lem3453900 A s x) (@lem3453899 A s x)). Qed.
Lemma lem3453931 {_89520 : Type'} (s : type686 _89520) (x : _89520) : (term0 _89520 x s) = (term1 _89520 s x).
Proof. exact (@lem3453930 _89520 s x). Qed.
Lemma lem3453932 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term2 _89520 _89534 x P f) = (term3 _89520 _89534 P f x).
Proof. exact (@lem3453931 _89520 (term4 _89520 _89534 P f) x). Qed.
Lemma lem3453942 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term5 _83064 x P) = (term6 _83064 P x).
Proof. exact (EQ_MP (@lem3453894 _83064 P x) (@lem3453893 _83064 P x)). Qed.
Lemma lem3453943 {_89520 : Type'} (P : type909 _89520) (x : _89520 -> Prop) : (term7 _89520 x P) = (term8 _89520 P x).
Proof. exact (@lem3453942 (_89520 -> Prop) P x). Qed.
Lemma lem3453944 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (t : _89520 -> Prop) : (term9 _89520 _89534 t P f) = (term10 _89520 _89534 P f t).
Proof. exact (@lem3453943 _89520 (term11 _89520 _89534 P f) t). Qed.
Lemma lem3453945 {_89520 _89534 : Type'} (GEN_PVAR_49 : _89520 -> Prop) (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term12 _89520 _89534 P f GEN_PVAR_49) = (term13 _89520 _89534 GEN_PVAR_49 P f).
Proof. exact (eq_refl (term12 _89520 _89534 P f GEN_PVAR_49)). Qed.
Lemma lem3453946 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term14 _89520 _89534 P f) = (term15 _89520 _89534 P f).
Proof. exact (fun_ext (fun GEN_PVAR_49 : _89520 -> Prop => @lem3453945 _89520 _89534 GEN_PVAR_49 P f)). Qed.
Lemma lem3453947 {_89520 : Type'} : (@GSPEC (_89520 -> Prop)) = (@GSPEC (_89520 -> Prop)).
Proof. exact (eq_refl (@GSPEC (_89520 -> Prop))). Qed.
Lemma lem3453948 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term16 _89520 _89534 P f) = (term4 _89520 _89534 P f).
Proof. exact (MK_COMB (@lem3453947 _89520) (@lem3453946 _89520 _89534 P f)). Qed.
Lemma lem3453949 {_89520 : Type'} (t : _89520 -> Prop) : (@IN (_89520 -> Prop) t) = (@IN (_89520 -> Prop) t).
Proof. exact (eq_refl (@IN (_89520 -> Prop) t)). Qed.
Lemma lem3453950 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term9 _89520 _89534 t P f) = (term17 _89520 _89534 t P f).
Proof. exact (MK_COMB (@lem3453949 _89520 t) (@lem3453948 _89520 _89534 P f)). Qed.
Lemma lem3453951 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3453952 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term18 _89520 _89534 t P f) = (term19 _89520 _89534 t P f).
Proof. exact (MK_COMB (@lem3453951) (@lem3453950 _89520 _89534 t P f)). Qed.
Lemma lem3453953 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term10 _89520 _89534 P f t) = (term20 _89520 _89534 t P f).
Proof. exact (eq_refl (term10 _89520 _89534 P f t)). Qed.
Lemma lem3453954 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (f : type1470 _89520 _89534) : ((term9 _89520 _89534 t P f) = (term10 _89520 _89534 P f t)) = ((term17 _89520 _89534 t P f) = (term20 _89520 _89534 t P f)).
Proof. exact (MK_COMB (@lem3453952 _89520 _89534 t P f) (@lem3453953 _89520 _89534 t P f)). Qed.
Lemma lem3453955 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term17 _89520 _89534 t P f) = (term20 _89520 _89534 t P f).
Proof. exact (EQ_MP (@lem3453954 _89520 _89534 t P f) (@lem3453944 _89520 _89534 P f t)). Qed.
Lemma lem3453961 {A B : Type'} (f : A -> B) (y : A) : (term21 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3453962 {_89520 : Type'} (f : type1527 _89520) (y : Prop) : (term22 _89520 f y) = (f y).
Proof. exact (@lem3453961 Prop (type686 _89520) f y). Qed.
Lemma lem3453963 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89534) : (term23 _89520 _89534 t P x) = (term24 _89520 _89534 t P x).
Proof. exact (@lem3453962 _89520 (term25 _89520 t) (P x)). Qed.
Lemma lem3453964 {_89520 : Type'} (p : Prop) (t : _89520 -> Prop) : (term26 _89520 t p) = (term27 _89520 p t).
Proof. exact (eq_refl (term26 _89520 t p)). Qed.
Lemma lem3453965 {_89520 : Type'} (t : _89520 -> Prop) : (term28 _89520 t) = (term25 _89520 t).
Proof. exact (fun_ext (fun p : Prop => @lem3453964 _89520 p t)). Qed.
Lemma lem3453966 {_89534 : Type'} (P : _89534 -> Prop) (x : _89534) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3453967 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89534) : (term23 _89520 _89534 t P x) = (term24 _89520 _89534 t P x).
Proof. exact (MK_COMB (@lem3453965 _89520 t) (@lem3453966 _89534 P x)). Qed.
Lemma lem3453968 {_89520 : Type'} : (@eq ((_89520 -> Prop) -> Prop)) = (@eq ((_89520 -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((_89520 -> Prop) -> Prop))). Qed.
Lemma lem3453969 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89534) : (term29 _89520 _89534 t P x) = (term30 _89520 _89534 t P x).
Proof. exact (MK_COMB (@lem3453968 _89520) (@lem3453967 _89520 _89534 t P x)). Qed.
Lemma lem3453970 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89534) (t : _89520 -> Prop) : (term24 _89520 _89534 t P x) = (term31 _89520 _89534 P x t).
Proof. exact (eq_refl (term24 _89520 _89534 t P x)). Qed.
Lemma lem3453971 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89534) (t : _89520 -> Prop) : ((term23 _89520 _89534 t P x) = (term24 _89520 _89534 t P x)) = ((term24 _89520 _89534 t P x) = (term31 _89520 _89534 P x t)).
Proof. exact (MK_COMB (@lem3453969 _89520 _89534 t P x) (@lem3453970 _89520 _89534 P x t)). Qed.
Lemma lem3453972 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89534) (t : _89520 -> Prop) : (term24 _89520 _89534 t P x) = (term31 _89520 _89534 P x t).
Proof. exact (EQ_MP (@lem3453971 _89520 _89534 P x t) (@lem3453963 _89520 _89534 t P x)). Qed.
Lemma lem3453977 {_89520 _89534 : Type'} (f : type1470 _89520 _89534) (x : _89534) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem3453978 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) (x : _89534) : (term32 _89520 _89534 t P f x) = (term33 _89520 _89534 P t f x).
Proof. exact (MK_COMB (@lem3453972 _89520 _89534 P x t) (@lem3453977 _89520 _89534 f x)). Qed.
Lemma lem3453980 {A B : Type'} (f : A -> B) (y : A) : (term21 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3453981 {_89520 : Type'} (f : type686 _89520) (y : _89520 -> Prop) : (term34 _89520 f y) = (f y).
Proof. exact (@lem3453980 (_89520 -> Prop) Prop f y). Qed.
Lemma lem3453982 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) (x : _89534) : (term35 _89520 _89534 P t f x) = (term33 _89520 _89534 P t f x).
Proof. exact (@lem3453981 _89520 (term31 _89520 _89534 P x t) (f x)). Qed.
Lemma lem3453983 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89534) (t : _89520 -> Prop) (t' : _89520 -> Prop) : (term36 _89520 _89534 P x t t') = (term37 _89520 _89534 P x t t').
Proof. exact (eq_refl (term36 _89520 _89534 P x t t')). Qed.
Lemma lem3453984 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89534) (t : _89520 -> Prop) : (term38 _89520 _89534 P x t) = (term31 _89520 _89534 P x t).
Proof. exact (fun_ext (fun t' : _89520 -> Prop => @lem3453983 _89520 _89534 P x t t')). Qed.
Lemma lem3453985 {_89520 _89534 : Type'} (f : type1470 _89520 _89534) (x : _89534) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem3453986 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) (x : _89534) : (term35 _89520 _89534 P t f x) = (term33 _89520 _89534 P t f x).
Proof. exact (MK_COMB (@lem3453984 _89520 _89534 P x t) (@lem3453985 _89520 _89534 f x)). Qed.
Lemma lem3453987 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3453988 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) (x : _89534) : (term39 _89520 _89534 P t f x) = (term40 _89520 _89534 P t f x).
Proof. exact (MK_COMB (@lem3453987) (@lem3453986 _89520 _89534 P t f x)). Qed.
Lemma lem3453989 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) (x : _89534) : (term33 _89520 _89534 P t f x) = (term41 _89520 _89534 P t f x).
Proof. exact (eq_refl (term33 _89520 _89534 P t f x)). Qed.
Lemma lem3453990 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) (x : _89534) : ((term35 _89520 _89534 P t f x) = (term33 _89520 _89534 P t f x)) = ((term33 _89520 _89534 P t f x) = (term41 _89520 _89534 P t f x)).
Proof. exact (MK_COMB (@lem3453988 _89520 _89534 P t f x) (@lem3453989 _89520 _89534 P t f x)). Qed.
Lemma lem3453991 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) (x : _89534) : (term33 _89520 _89534 P t f x) = (term41 _89520 _89534 P t f x).
Proof. exact (EQ_MP (@lem3453990 _89520 _89534 P t f x) (@lem3453982 _89520 _89534 P t f x)). Qed.
Lemma lem3453996 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) (x : _89534) : (term32 _89520 _89534 t P f x) = (term41 _89520 _89534 P t f x).
Proof. exact (TRANS (@lem3453978 _89520 _89534 P t f x) (@lem3453991 _89520 _89534 P t f x)). Qed.
Lemma lem3453997 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) : (term42 _89520 _89534 t P f) = (term43 _89520 _89534 P t f).
Proof. exact (fun_ext (fun x : _89534 => @lem3453996 _89520 _89534 P t f x)). Qed.
Lemma lem3453998 {_89534 : Type'} : (@ex _89534) = (@ex _89534).
Proof. exact (eq_refl (@ex _89534)). Qed.
Lemma lem3453999 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) : (term20 _89520 _89534 t P f) = (term44 _89520 _89534 P t f).
Proof. exact (MK_COMB (@lem3453998 _89534) (@lem3453997 _89520 _89534 P t f)). Qed.
Lemma lem3454004 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) : (term17 _89520 _89534 t P f) = (term44 _89520 _89534 P t f).
Proof. exact (TRANS (@lem3453955 _89520 _89534 t P f) (@lem3453999 _89520 _89534 P t f)). Qed.
Lemma lem3454005 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3454006 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) : (term45 _89520 _89534 t P f) = (term46 _89520 _89534 P t f).
Proof. exact (MK_COMB (@lem3454005) (@lem3454004 _89520 _89534 P t f)). Qed.
Lemma lem3454007 {_89520 : Type'} (x : _89520) (t : _89520 -> Prop) : (@IN _89520 x t) = (@IN _89520 x t).
Proof. exact (eq_refl (@IN _89520 x t)). Qed.
Lemma lem3454008 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term47 _89520 _89534 P f x t) = (term48 _89520 _89534 P f x t).
Proof. exact (MK_COMB (@lem3454006 _89520 _89534 P t f) (@lem3454007 _89520 x t)). Qed.
Lemma lem3454011 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term49 _89520 _89534 P f x) = (term50 _89520 _89534 P f x).
Proof. exact (fun_ext (fun t : _89520 -> Prop => @lem3454008 _89520 _89534 P f x t)). Qed.
Lemma lem3454012 {_89520 : Type'} : (@ex (_89520 -> Prop)) = (@ex (_89520 -> Prop)).
Proof. exact (eq_refl (@ex (_89520 -> Prop))). Qed.
Lemma lem3454013 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term3 _89520 _89534 P f x) = (term51 _89520 _89534 P f x).
Proof. exact (MK_COMB (@lem3454012 _89520) (@lem3454011 _89520 _89534 P f x)). Qed.
Lemma lem3454018 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term2 _89520 _89534 x P f) = (term51 _89520 _89534 P f x).
Proof. exact (TRANS (@lem3453932 _89520 _89534 P f x) (@lem3454013 _89520 _89534 P f x)). Qed.
Lemma lem3454019 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3454020 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term52 _89520 _89534 x P f) = (term53 _89520 _89534 P f x).
Proof. exact (MK_COMB (@lem3454019) (@lem3454018 _89520 _89534 P f x)). Qed.
Lemma lem3454022 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term54 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3453887 _83095 p x) (@lem3453886 _83095 p x)). Qed.
Lemma lem3454023 {_89520 : Type'} (p : _89520 -> Prop) (x : _89520) : (term54 _89520 x p) = (p x).
Proof. exact (@lem3454022 _89520 p x). Qed.
Lemma lem3454024 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term55 _89520 _89534 x P f) = (term56 _89520 _89534 P f x).
Proof. exact (@lem3454023 _89520 (term57 _89520 _89534 P f) x). Qed.
Lemma lem3454025 {_89520 _89534 : Type'} (P : _89534 -> Prop) (a : _89520) (f : type1470 _89520 _89534) : (term56 _89520 _89534 P f a) = (term58 _89520 _89534 P a f).
Proof. exact (eq_refl (term56 _89520 _89534 P f a)). Qed.
Lemma lem3454026 {_89520 : Type'} (GEN_PVAR_50 : _89520) : (@SETSPEC _89520 GEN_PVAR_50) = (@SETSPEC _89520 GEN_PVAR_50).
Proof. exact (eq_refl (@SETSPEC _89520 GEN_PVAR_50)). Qed.
Lemma lem3454027 {_89520 _89534 : Type'} (GEN_PVAR_50 : _89520) (P : _89534 -> Prop) (a : _89520) (f : type1470 _89520 _89534) : (term59 _89520 _89534 GEN_PVAR_50 P f a) = (term60 _89520 _89534 GEN_PVAR_50 P a f).
Proof. exact (MK_COMB (@lem3454026 _89520 GEN_PVAR_50) (@lem3454025 _89520 _89534 P a f)). Qed.
Lemma lem3454028 {_89520 : Type'} (a : _89520) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3454029 {_89520 _89534 : Type'} (GEN_PVAR_50 : _89520) (P : _89534 -> Prop) (f : type1470 _89520 _89534) (a : _89520) : (term61 _89520 _89534 GEN_PVAR_50 P f a) = (term62 _89520 _89534 GEN_PVAR_50 P f a).
Proof. exact (MK_COMB (@lem3454027 _89520 _89534 GEN_PVAR_50 P a f) (@lem3454028 _89520 a)). Qed.
Lemma lem3454030 {_89520 _89534 : Type'} (GEN_PVAR_50 : _89520) (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term63 _89520 _89534 GEN_PVAR_50 P f) = (term64 _89520 _89534 GEN_PVAR_50 P f).
Proof. exact (fun_ext (fun a : _89520 => @lem3454029 _89520 _89534 GEN_PVAR_50 P f a)). Qed.
Lemma lem3454031 {_89520 : Type'} : (@ex _89520) = (@ex _89520).
Proof. exact (eq_refl (@ex _89520)). Qed.
Lemma lem3454032 {_89520 _89534 : Type'} (GEN_PVAR_50 : _89520) (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term65 _89520 _89534 GEN_PVAR_50 P f) = (term66 _89520 _89534 GEN_PVAR_50 P f).
Proof. exact (MK_COMB (@lem3454031 _89520) (@lem3454030 _89520 _89534 GEN_PVAR_50 P f)). Qed.
Lemma lem3454033 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term67 _89520 _89534 P f) = (term68 _89520 _89534 P f).
Proof. exact (fun_ext (fun GEN_PVAR_50 : _89520 => @lem3454032 _89520 _89534 GEN_PVAR_50 P f)). Qed.
Lemma lem3454034 {_89520 : Type'} : (@GSPEC _89520) = (@GSPEC _89520).
Proof. exact (eq_refl (@GSPEC _89520)). Qed.
Lemma lem3454035 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term69 _89520 _89534 P f) = (term70 _89520 _89534 P f).
Proof. exact (MK_COMB (@lem3454034 _89520) (@lem3454033 _89520 _89534 P f)). Qed.
Lemma lem3454036 {_89520 : Type'} (x : _89520) : (@IN _89520 x) = (@IN _89520 x).
Proof. exact (eq_refl (@IN _89520 x)). Qed.
Lemma lem3454037 {_89520 _89534 : Type'} (x : _89520) (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term55 _89520 _89534 x P f) = (term71 _89520 _89534 x P f).
Proof. exact (MK_COMB (@lem3454036 _89520 x) (@lem3454035 _89520 _89534 P f)). Qed.
Lemma lem3454038 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3454039 {_89520 _89534 : Type'} (x : _89520) (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term72 _89520 _89534 x P f) = (term73 _89520 _89534 x P f).
Proof. exact (MK_COMB (@lem3454038) (@lem3454037 _89520 _89534 x P f)). Qed.
Lemma lem3454040 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term56 _89520 _89534 P f x) = (term58 _89520 _89534 P x f).
Proof. exact (eq_refl (term56 _89520 _89534 P f x)). Qed.
Lemma lem3454041 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : ((term55 _89520 _89534 x P f) = (term56 _89520 _89534 P f x)) = ((term71 _89520 _89534 x P f) = (term58 _89520 _89534 P x f)).
Proof. exact (MK_COMB (@lem3454039 _89520 _89534 x P f) (@lem3454040 _89520 _89534 P x f)). Qed.
Lemma lem3454042 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term71 _89520 _89534 x P f) = (term58 _89520 _89534 P x f).
Proof. exact (EQ_MP (@lem3454041 _89520 _89534 P x f) (@lem3454024 _89520 _89534 P f x)). Qed.
Lemma lem3454049 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : ((term2 _89520 _89534 x P f) = (term71 _89520 _89534 x P f)) = ((term51 _89520 _89534 P f x) = (term58 _89520 _89534 P x f)).
Proof. exact (MK_COMB (@lem3454020 _89520 _89534 P f x) (@lem3454042 _89520 _89534 P x f)). Qed.
Lemma lem3454052 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term74 _89520 _89534 P f) = (term75 _89520 _89534 P f).
Proof. exact (fun_ext (fun x : _89520 => @lem3454049 _89520 _89534 P x f)). Qed.
Lemma lem3454053 {_89520 : Type'} : (@all _89520) = (@all _89520).
Proof. exact (eq_refl (@all _89520)). Qed.
Lemma lem3454054 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term76 _89520 _89534 P f) = (term77 _89520 _89534 P f).
Proof. exact (MK_COMB (@lem3454053 _89520) (@lem3454052 _89520 _89534 P f)). Qed.
Lemma lem3454059 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term77 _89520 _89534 P f) = (term76 _89520 _89534 P f).
Proof. exact (SYM (@lem3454054 _89520 _89534 P f)). Qed.
