Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IN_UNIONS_term_abbrevs.
Require Import UNIONS_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Lemma lem3204950 {A : Type'} (s : type686 A) : term0 A s.
Proof. exact (@lem3189257 A s). Qed.
Lemma lem3204951 {A : Type'} (s : type686 A) : (term0 A s) = ((@UNIONS A s) = (term1 A s)).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3204977 {_83095 : Type'} : term2 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem3204978 {_83095 : Type'} (p : _83095 -> Prop) : term3 _83095 p.
Proof. exact (@lem3204977 _83095 p). Qed.
Lemma lem3204979 {_83095 : Type'} (p : _83095 -> Prop) : (term3 _83095 p) = (term4 _83095 p).
Proof. exact (eq_refl (term3 _83095 p)). Qed.
Lemma lem3204980 {_83095 : Type'} (p : _83095 -> Prop) : term4 _83095 p.
Proof. exact (EQ_MP (@lem3204979 _83095 p) (@lem3204978 _83095 p)). Qed.
Lemma lem3204981 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term5 _83095 p x.
Proof. exact (@lem3204980 _83095 p x). Qed.
Lemma lem3204982 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term5 _83095 p x) = ((term6 _83095 x p) = (p x)).
Proof. exact (eq_refl (term5 _83095 p x)). Qed.
Lemma lem3205002 {A : Type'} (s : type686 A) : (@UNIONS A s) = (term1 A s).
Proof. exact (EQ_MP (@lem3204951 A s) (@lem3204950 A s)). Qed.
Lemma lem3205003 {A : Type'} (s : type686 A) : (@UNIONS A s) = (term1 A s).
Proof. exact (@lem3205002 A s). Qed.
Lemma lem3205014 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3205015 {A : Type'} (x : A) (s : type686 A) : (term7 A x s) = (term8 A x s).
Proof. exact (MK_COMB (@lem3205014 A x) (@lem3205003 A s)). Qed.
Lemma lem3205017 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term6 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3204982 _83095 p x) (@lem3204981 _83095 p x)). Qed.
Lemma lem3205018 {A : Type'} (p : A -> Prop) (x : A) : (term6 A x p) = (p x).
Proof. exact (@lem3205017 A p x). Qed.
Lemma lem3205019 {A : Type'} (s : type686 A) (x : A) : (term9 A x s) = (term10 A s x).
Proof. exact (@lem3205018 A (term11 A s) x). Qed.
Lemma lem3205020 {A : Type'} (s : type686 A) (x : A) : (term10 A s x) = (term12 A s x).
Proof. exact (eq_refl (term10 A s x)). Qed.
Lemma lem3205021 {A : Type'} (GEN_PVAR_1 : A) : (@SETSPEC A GEN_PVAR_1) = (@SETSPEC A GEN_PVAR_1).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_1)). Qed.
Lemma lem3205022 {A : Type'} (GEN_PVAR_1 : A) (s : type686 A) (x : A) : (term13 A GEN_PVAR_1 s x) = (term14 A GEN_PVAR_1 s x).
Proof. exact (MK_COMB (@lem3205021 A GEN_PVAR_1) (@lem3205020 A s x)). Qed.
Lemma lem3205023 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3205024 {A : Type'} (GEN_PVAR_1 : A) (s : type686 A) (x : A) : (term15 A GEN_PVAR_1 s x) = (term16 A GEN_PVAR_1 s x).
Proof. exact (MK_COMB (@lem3205022 A GEN_PVAR_1 s x) (@lem3205023 A x)). Qed.
Lemma lem3205025 {A : Type'} (GEN_PVAR_1 : A) (s : type686 A) : (term17 A GEN_PVAR_1 s) = (term18 A GEN_PVAR_1 s).
Proof. exact (fun_ext (fun x : A => @lem3205024 A GEN_PVAR_1 s x)). Qed.
Lemma lem3205026 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3205027 {A : Type'} (GEN_PVAR_1 : A) (s : type686 A) : (term19 A GEN_PVAR_1 s) = (term20 A GEN_PVAR_1 s).
Proof. exact (MK_COMB (@lem3205026 A) (@lem3205025 A GEN_PVAR_1 s)). Qed.
Lemma lem3205028 {A : Type'} (s : type686 A) : (term21 A s) = (term22 A s).
Proof. exact (fun_ext (fun GEN_PVAR_1 : A => @lem3205027 A GEN_PVAR_1 s)). Qed.
Lemma lem3205029 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3205030 {A : Type'} (s : type686 A) : (term23 A s) = (term1 A s).
Proof. exact (MK_COMB (@lem3205029 A) (@lem3205028 A s)). Qed.
Lemma lem3205031 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3205032 {A : Type'} (x : A) (s : type686 A) : (term9 A x s) = (term8 A x s).
Proof. exact (MK_COMB (@lem3205031 A x) (@lem3205030 A s)). Qed.
Lemma lem3205033 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3205034 {A : Type'} (x : A) (s : type686 A) : (term24 A x s) = (term25 A x s).
Proof. exact (MK_COMB (@lem3205033) (@lem3205032 A x s)). Qed.
Lemma lem3205035 {A : Type'} (s : type686 A) (x : A) : (term10 A s x) = (term12 A s x).
Proof. exact (eq_refl (term10 A s x)). Qed.
Lemma lem3205036 {A : Type'} (s : type686 A) (x : A) : ((term9 A x s) = (term10 A s x)) = ((term8 A x s) = (term12 A s x)).
Proof. exact (MK_COMB (@lem3205034 A x s) (@lem3205035 A s x)). Qed.
Lemma lem3205037 {A : Type'} (s : type686 A) (x : A) : (term8 A x s) = (term12 A s x).
Proof. exact (EQ_MP (@lem3205036 A s x) (@lem3205019 A s x)). Qed.
Lemma lem3205044 {A : Type'} (s : type686 A) (x : A) : (term7 A x s) = (term12 A s x).
Proof. exact (TRANS (@lem3205015 A x s) (@lem3205037 A s x)). Qed.
Lemma lem3205045 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3205046 {A : Type'} (s : type686 A) (x : A) : (term26 A x s) = (term27 A s x).
Proof. exact (MK_COMB (@lem3205045) (@lem3205044 A s x)). Qed.
Lemma lem3205053 {A : Type'} (s : type686 A) (x : A) : (term12 A s x) = (term12 A s x).
Proof. exact (eq_refl (term12 A s x)). Qed.
Lemma lem3205054 {A : Type'} (s : type686 A) (x : A) : ((term7 A x s) = (term12 A s x)) = ((term12 A s x) = (term12 A s x)).
Proof. exact (MK_COMB (@lem3205046 A s x) (@lem3205053 A s x)). Qed.
Lemma lem3205056 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3205057 (x : Prop) : (x = x) = True.
Proof. exact (@lem3205056 Prop x). Qed.
Lemma lem3205058 {A : Type'} (s : type686 A) (x : A) : ((term12 A s x) = (term12 A s x)) = True.
Proof. exact (@lem3205057 (term12 A s x)). Qed.
Lemma lem3205061 {A : Type'} (s : type686 A) (x : A) : (term28 A s x) = (term28 A s x).
Proof. exact (eq_refl (term28 A s x)). Qed.
Lemma lem3205062 {A : Type'} (s : type686 A) (x : A) : (term28 A s x) = (((term12 A s x) = (term12 A s x)) = True).
Proof. exact (eq_refl (term28 A s x)). Qed.
Lemma lem3205063 {A : Type'} (s : type686 A) (x : A) : (term29 A s x) = (term29 A s x).
Proof. exact (eq_refl (term29 A s x)). Qed.
Lemma lem3205064 {A : Type'} (s : type686 A) (x : A) : ((term28 A s x) = (term28 A s x)) = ((term28 A s x) = (((term12 A s x) = (term12 A s x)) = True)).
Proof. exact (MK_COMB (@lem3205063 A s x) (@lem3205062 A s x)). Qed.
Lemma lem3205065 {A : Type'} (s : type686 A) (x : A) : (term28 A s x) = (((term12 A s x) = (term12 A s x)) = True).
Proof. exact (eq_refl (term28 A s x)). Qed.
Lemma lem3205066 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3205067 {A : Type'} (s : type686 A) (x : A) : (term29 A s x) = (term30 A s x).
Proof. exact (MK_COMB (@lem3205066) (@lem3205065 A s x)). Qed.
Lemma lem3205068 {A : Type'} (s : type686 A) (x : A) : (((term12 A s x) = (term12 A s x)) = True) = (((term12 A s x) = (term12 A s x)) = True).
Proof. exact (eq_refl (((term12 A s x) = (term12 A s x)) = True)). Qed.
Lemma lem3205069 {A : Type'} (s : type686 A) (x : A) : ((term28 A s x) = (((term12 A s x) = (term12 A s x)) = True)) = ((((term12 A s x) = (term12 A s x)) = True) = (((term12 A s x) = (term12 A s x)) = True)).
Proof. exact (MK_COMB (@lem3205067 A s x) (@lem3205068 A s x)). Qed.
Lemma lem3205070 {A : Type'} (s : type686 A) (x : A) : ((term28 A s x) = (term28 A s x)) = ((((term12 A s x) = (term12 A s x)) = True) = (((term12 A s x) = (term12 A s x)) = True)).
Proof. exact (TRANS (@lem3205064 A s x) (@lem3205069 A s x)). Qed.
Lemma lem3205071 {A : Type'} (s : type686 A) (x : A) : (((term12 A s x) = (term12 A s x)) = True) = (((term12 A s x) = (term12 A s x)) = True).
Proof. exact (EQ_MP (@lem3205070 A s x) (@lem3205061 A s x)). Qed.
Lemma lem3205072 {A : Type'} (s : type686 A) (x : A) : ((term12 A s x) = (term12 A s x)) = True.
Proof. exact (EQ_MP (@lem3205071 A s x) (@lem3205058 A s x)). Qed.
Lemma lem3205073 {A : Type'} (s : type686 A) (x : A) : ((term7 A x s) = (term12 A s x)) = True.
Proof. exact (TRANS (@lem3205054 A s x) (@lem3205072 A s x)). Qed.
Lemma lem3205074 {A : Type'} (s : type686 A) : (term31 A s) = (term32 A).
Proof. exact (fun_ext (fun x : A => @lem3205073 A s x)). Qed.
Lemma lem3205075 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3205076 {A : Type'} (s : type686 A) : (term33 A s) = (term34 A).
Proof. exact (MK_COMB (@lem3205075 A) (@lem3205074 A s)). Qed.
Lemma lem3205078 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3205079 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (@lem3205078 A t). Qed.
Lemma lem3205080 {A : Type'} : (term34 A) = True.
Proof. exact (@lem3205079 A True). Qed.
Lemma lem3205081 {A : Type'} (s : type686 A) : (term33 A s) = True.
Proof. exact (TRANS (@lem3205076 A s) (@lem3205080 A)). Qed.
Lemma lem3205082 {A : Type'} : (term36 A) = (term37 A).
Proof. exact (fun_ext (fun s : type686 A => @lem3205081 A s)). Qed.
Lemma lem3205083 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3205084 {A : Type'} : (term38 A) = (term39 A).
Proof. exact (MK_COMB (@lem3205083 A) (@lem3205082 A)). Qed.
Lemma lem3205086 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3205087 {A : Type'} (t : Prop) : (term40 A t) = t.
Proof. exact (@lem3205086 (type686 A) t). Qed.
Lemma lem3205088 {A : Type'} : (term39 A) = True.
Proof. exact (@lem3205087 A True). Qed.
Lemma lem3205089 {A : Type'} : (term38 A) = True.
Proof. exact (TRANS (@lem3205084 A) (@lem3205088 A)). Qed.
Lemma lem3205090 {A : Type'} : True = (term38 A).
Proof. exact (SYM (@lem3205089 A)). Qed.
Lemma lem3205091 {A : Type'} : term38 A.
Proof. exact (EQ_MP (@lem3205090 A) (@lem0)). Qed.
