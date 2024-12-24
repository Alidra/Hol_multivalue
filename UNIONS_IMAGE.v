Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNIONS_IMAGE_term_abbrevs.
Require Import DISJ_ASSOC_spec.
Require Import EXTENSION_spec.
Require Import IN_IMAGE_spec.
Require Import IN_UNIONS_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Lemma lem3450828 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3450829 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3450830 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3450829 t1) (@lem3450828 t1)). Qed.
Lemma lem3450831 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3450830 t1 t2). Qed.
Lemma lem3450832 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3450833 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3450832 t1 t2) (@lem3450831 t1 t2)). Qed.
Lemma lem3450834 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3450833 t1 t2 t3). Qed.
Lemma lem3450835 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3450836 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3450835 t1 t2 t3) (@lem3450834 t1 t2 t3)). Qed.
Lemma lem3450837 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3450836 t1 t2 t3)). Qed.
Lemma lem3450862 {_83095 : Type'} : term7 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem3450863 {_83095 : Type'} (p : _83095 -> Prop) : term8 _83095 p.
Proof. exact (@lem3450862 _83095 p). Qed.
Lemma lem3450864 {_83095 : Type'} (p : _83095 -> Prop) : (term8 _83095 p) = (term9 _83095 p).
Proof. exact (eq_refl (term8 _83095 p)). Qed.
Lemma lem3450865 {_83095 : Type'} (p : _83095 -> Prop) : term9 _83095 p.
Proof. exact (EQ_MP (@lem3450864 _83095 p) (@lem3450863 _83095 p)). Qed.
Lemma lem3450866 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term10 _83095 p x.
Proof. exact (@lem3450865 _83095 p x). Qed.
Lemma lem3450867 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term10 _83095 p x) = ((term11 _83095 x p) = (p x)).
Proof. exact (eq_refl (term10 _83095 p x)). Qed.
Lemma lem3450876 {A B : Type'} (y : B) : term12 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem3450877 {A B : Type'} (y : B) : (term12 A B y) = (term13 A B y).
Proof. exact (eq_refl (term12 A B y)). Qed.
Lemma lem3450878 {A B : Type'} (y : B) : term13 A B y.
Proof. exact (EQ_MP (@lem3450877 A B y) (@lem3450876 A B y)). Qed.
Lemma lem3450879 {A B : Type'} (y : B) (s : A -> Prop) : term14 A B y s.
Proof. exact (@lem3450878 A B y s). Qed.
Lemma lem3450880 {A B : Type'} (y : B) (s : A -> Prop) : (term14 A B y s) = (term15 A B y s).
Proof. exact (eq_refl (term14 A B y s)). Qed.
Lemma lem3450881 {A B : Type'} (y : B) (s : A -> Prop) : term15 A B y s.
Proof. exact (EQ_MP (@lem3450880 A B y s) (@lem3450879 A B y s)). Qed.
Lemma lem3450882 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term16 A B y s f.
Proof. exact (@lem3450881 A B y s f). Qed.
Lemma lem3450883 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term16 A B y s f) = ((term17 A B y f s) = (term18 A B y f s)).
Proof. exact (eq_refl (term16 A B y s f)). Qed.
Lemma lem3450885 {A : Type'} (s : type686 A) : term19 A s.
Proof. exact (@lem3205091 A s). Qed.
Lemma lem3450886 {A : Type'} (s : type686 A) : (term19 A s) = (term20 A s).
Proof. exact (eq_refl (term19 A s)). Qed.
Lemma lem3450887 {A : Type'} (s : type686 A) : term20 A s.
Proof. exact (EQ_MP (@lem3450886 A s) (@lem3450885 A s)). Qed.
Lemma lem3450888 {A : Type'} (s : type686 A) (x : A) : term21 A s x.
Proof. exact (@lem3450887 A s x). Qed.
Lemma lem3450889 {A : Type'} (s : type686 A) (x : A) : (term21 A s x) = ((term22 A x s) = (term23 A s x)).
Proof. exact (eq_refl (term21 A s x)). Qed.
Lemma lem3450891 {A : Type'} (s : A -> Prop) : term24 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem3450892 {A : Type'} (s : A -> Prop) : (term24 A s) = (term25 A s).
Proof. exact (eq_refl (term24 A s)). Qed.
Lemma lem3450893 {A : Type'} (s : A -> Prop) : term25 A s.
Proof. exact (EQ_MP (@lem3450892 A s) (@lem3450891 A s)). Qed.
Lemma lem3450894 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term26 A s t.
Proof. exact (@lem3450893 A s t). Qed.
Lemma lem3450895 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term26 A s t) = ((s = t) = (term27 A s t)).
Proof. exact (eq_refl (term26 A s t)). Qed.
Lemma lem3450898 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term27 A s t).
Proof. exact (EQ_MP (@lem3450895 A s t) (@lem3450894 A s t)). Qed.
Lemma lem3450899 {_89422 : Type'} (s : _89422 -> Prop) (t : _89422 -> Prop) : (s = t) = (term27 _89422 s t).
Proof. exact (@lem3450898 _89422 s t). Qed.
Lemma lem3450900 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : ((term28 _89422 _89438 f s) = (term29 _89422 _89438 s f)) = (term30 _89422 _89438 s f).
Proof. exact (@lem3450899 _89422 (term28 _89422 _89438 f s) (term29 _89422 _89438 s f)). Qed.
Lemma lem3450901 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term30 _89422 _89438 s f) = ((term28 _89422 _89438 f s) = (term29 _89422 _89438 s f)).
Proof. exact (SYM (@lem3450900 _89422 _89438 s f)). Qed.
Lemma lem3450909 {A : Type'} (s : type686 A) (x : A) : (term22 A x s) = (term23 A s x).
Proof. exact (EQ_MP (@lem3450889 A s x) (@lem3450888 A s x)). Qed.
Lemma lem3450910 {_89422 : Type'} (s : type686 _89422) (x : _89422) : (term22 _89422 x s) = (term23 _89422 s x).
Proof. exact (@lem3450909 _89422 s x). Qed.
Lemma lem3450911 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term31 _89422 _89438 x f s) = (term32 _89422 _89438 f s x).
Proof. exact (@lem3450910 _89422 (@IMAGE _89438 (_89422 -> Prop) f s) x). Qed.
Lemma lem3450919 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term17 A B y f s) = (term18 A B y f s).
Proof. exact (EQ_MP (@lem3450883 A B y f s) (@lem3450882 A B y s f)). Qed.
Lemma lem3450920 {_89422 _89438 : Type'} (y : _89422 -> Prop) (f : type1470 _89422 _89438) (s : _89438 -> Prop) : (term33 _89422 _89438 y f s) = (term34 _89422 _89438 y f s).
Proof. exact (@lem3450919 _89438 (_89422 -> Prop) y f s). Qed.
Lemma lem3450921 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (s : _89438 -> Prop) : (term33 _89422 _89438 t f s) = (term34 _89422 _89438 t f s).
Proof. exact (@lem3450920 _89422 _89438 t f s). Qed.
Lemma lem3450930 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3450931 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (s : _89438 -> Prop) : (term35 _89422 _89438 t f s) = (term36 _89422 _89438 t f s).
Proof. exact (MK_COMB (@lem3450930) (@lem3450921 _89422 _89438 t f s)). Qed.
Lemma lem3450932 {_89422 : Type'} (x : _89422) (t : _89422 -> Prop) : (@IN _89422 x t) = (@IN _89422 x t).
Proof. exact (eq_refl (@IN _89422 x t)). Qed.
Lemma lem3450933 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term37 _89422 _89438 f s x t) = (term38 _89422 _89438 f s x t).
Proof. exact (MK_COMB (@lem3450931 _89422 _89438 t f s) (@lem3450932 _89422 x t)). Qed.
Lemma lem3450936 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term39 _89422 _89438 f s x) = (term40 _89422 _89438 f s x).
Proof. exact (fun_ext (fun t : _89422 -> Prop => @lem3450933 _89422 _89438 f s x t)). Qed.
Lemma lem3450937 {_89422 : Type'} : (@ex (_89422 -> Prop)) = (@ex (_89422 -> Prop)).
Proof. exact (eq_refl (@ex (_89422 -> Prop))). Qed.
Lemma lem3450938 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term32 _89422 _89438 f s x) = (term41 _89422 _89438 f s x).
Proof. exact (MK_COMB (@lem3450937 _89422) (@lem3450936 _89422 _89438 f s x)). Qed.
Lemma lem3450943 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term31 _89422 _89438 x f s) = (term41 _89422 _89438 f s x).
Proof. exact (TRANS (@lem3450911 _89422 _89438 f s x) (@lem3450938 _89422 _89438 f s x)). Qed.
Lemma lem3450944 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3450945 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term42 _89422 _89438 x f s) = (term43 _89422 _89438 f s x).
Proof. exact (MK_COMB (@lem3450944) (@lem3450943 _89422 _89438 f s x)). Qed.
Lemma lem3450947 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term11 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3450867 _83095 p x) (@lem3450866 _83095 p x)). Qed.
Lemma lem3450948 {_89422 : Type'} (p : _89422 -> Prop) (x : _89422) : (term11 _89422 x p) = (p x).
Proof. exact (@lem3450947 _89422 p x). Qed.
Lemma lem3450949 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) (x : _89422) : (term44 _89422 _89438 x s f) = (term45 _89422 _89438 s f x).
Proof. exact (@lem3450948 _89422 (term46 _89422 _89438 s f) x). Qed.
Lemma lem3450950 {_89422 _89438 : Type'} (s : _89438 -> Prop) (y : _89422) (f : type1470 _89422 _89438) : (term45 _89422 _89438 s f y) = (term47 _89422 _89438 s y f).
Proof. exact (eq_refl (term45 _89422 _89438 s f y)). Qed.
Lemma lem3450951 {_89422 : Type'} (GEN_PVAR_47 : _89422) : (@SETSPEC _89422 GEN_PVAR_47) = (@SETSPEC _89422 GEN_PVAR_47).
Proof. exact (eq_refl (@SETSPEC _89422 GEN_PVAR_47)). Qed.
Lemma lem3450952 {_89422 _89438 : Type'} (GEN_PVAR_47 : _89422) (s : _89438 -> Prop) (y : _89422) (f : type1470 _89422 _89438) : (term48 _89422 _89438 GEN_PVAR_47 s f y) = (term49 _89422 _89438 GEN_PVAR_47 s y f).
Proof. exact (MK_COMB (@lem3450951 _89422 GEN_PVAR_47) (@lem3450950 _89422 _89438 s y f)). Qed.
Lemma lem3450953 {_89422 : Type'} (y : _89422) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3450954 {_89422 _89438 : Type'} (GEN_PVAR_47 : _89422) (s : _89438 -> Prop) (f : type1470 _89422 _89438) (y : _89422) : (term50 _89422 _89438 GEN_PVAR_47 s f y) = (term51 _89422 _89438 GEN_PVAR_47 s f y).
Proof. exact (MK_COMB (@lem3450952 _89422 _89438 GEN_PVAR_47 s y f) (@lem3450953 _89422 y)). Qed.
Lemma lem3450955 {_89422 _89438 : Type'} (GEN_PVAR_47 : _89422) (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term52 _89422 _89438 GEN_PVAR_47 s f) = (term53 _89422 _89438 GEN_PVAR_47 s f).
Proof. exact (fun_ext (fun y : _89422 => @lem3450954 _89422 _89438 GEN_PVAR_47 s f y)). Qed.
Lemma lem3450956 {_89422 : Type'} : (@ex _89422) = (@ex _89422).
Proof. exact (eq_refl (@ex _89422)). Qed.
Lemma lem3450957 {_89422 _89438 : Type'} (GEN_PVAR_47 : _89422) (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term54 _89422 _89438 GEN_PVAR_47 s f) = (term55 _89422 _89438 GEN_PVAR_47 s f).
Proof. exact (MK_COMB (@lem3450956 _89422) (@lem3450955 _89422 _89438 GEN_PVAR_47 s f)). Qed.
Lemma lem3450958 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term56 _89422 _89438 s f) = (term57 _89422 _89438 s f).
Proof. exact (fun_ext (fun GEN_PVAR_47 : _89422 => @lem3450957 _89422 _89438 GEN_PVAR_47 s f)). Qed.
Lemma lem3450959 {_89422 : Type'} : (@GSPEC _89422) = (@GSPEC _89422).
Proof. exact (eq_refl (@GSPEC _89422)). Qed.
Lemma lem3450960 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term58 _89422 _89438 s f) = (term29 _89422 _89438 s f).
Proof. exact (MK_COMB (@lem3450959 _89422) (@lem3450958 _89422 _89438 s f)). Qed.
Lemma lem3450961 {_89422 : Type'} (x : _89422) : (@IN _89422 x) = (@IN _89422 x).
Proof. exact (eq_refl (@IN _89422 x)). Qed.
Lemma lem3450962 {_89422 _89438 : Type'} (x : _89422) (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term44 _89422 _89438 x s f) = (term59 _89422 _89438 x s f).
Proof. exact (MK_COMB (@lem3450961 _89422 x) (@lem3450960 _89422 _89438 s f)). Qed.
Lemma lem3450963 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3450964 {_89422 _89438 : Type'} (x : _89422) (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term60 _89422 _89438 x s f) = (term61 _89422 _89438 x s f).
Proof. exact (MK_COMB (@lem3450963) (@lem3450962 _89422 _89438 x s f)). Qed.
Lemma lem3450965 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term45 _89422 _89438 s f x) = (term47 _89422 _89438 s x f).
Proof. exact (eq_refl (term45 _89422 _89438 s f x)). Qed.
Lemma lem3450966 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : ((term44 _89422 _89438 x s f) = (term45 _89422 _89438 s f x)) = ((term59 _89422 _89438 x s f) = (term47 _89422 _89438 s x f)).
Proof. exact (MK_COMB (@lem3450964 _89422 _89438 x s f) (@lem3450965 _89422 _89438 s x f)). Qed.
Lemma lem3450967 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term59 _89422 _89438 x s f) = (term47 _89422 _89438 s x f).
Proof. exact (EQ_MP (@lem3450966 _89422 _89438 s x f) (@lem3450949 _89422 _89438 s f x)). Qed.
Lemma lem3450974 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : ((term31 _89422 _89438 x f s) = (term59 _89422 _89438 x s f)) = ((term41 _89422 _89438 f s x) = (term47 _89422 _89438 s x f)).
Proof. exact (MK_COMB (@lem3450945 _89422 _89438 f s x) (@lem3450967 _89422 _89438 s x f)). Qed.
Lemma lem3450977 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term62 _89422 _89438 s f) = (term63 _89422 _89438 s f).
Proof. exact (fun_ext (fun x : _89422 => @lem3450974 _89422 _89438 s x f)). Qed.
Lemma lem3450978 {_89422 : Type'} : (@all _89422) = (@all _89422).
Proof. exact (eq_refl (@all _89422)). Qed.
Lemma lem3450979 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term30 _89422 _89438 s f) = (term64 _89422 _89438 s f).
Proof. exact (MK_COMB (@lem3450978 _89422) (@lem3450977 _89422 _89438 s f)). Qed.
Lemma lem3450984 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term64 _89422 _89438 s f) = (term30 _89422 _89438 s f).
Proof. exact (SYM (@lem3450979 _89422 _89438 s f)). Qed.
Lemma lem3450986 (p : Prop) : p = (term65 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3450987 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term64 _89422 _89438 s f) = (term66 _89422 _89438 s f).
Proof. exact (@lem3450986 (term64 _89422 _89438 s f)). Qed.
Lemma lem3450988 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term66 _89422 _89438 s f) = (term64 _89422 _89438 s f).
Proof. exact (SYM (@lem3450987 _89422 _89438 s f)). Qed.
Lemma lem3450989 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) (h1 : term67 _89422 _89438 s f) : term67 _89422 _89438 s f.
Proof. exact (h1). Qed.
Lemma lem3450992 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) (h1 : term66 _89422 _89438 s f) : term66 _89422 _89438 s f.
Proof. exact (h1). Qed.
Lemma lem3450993 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : term68 _89422 _89438 s f.
Proof. exact (fun h0 : term66 _89422 _89438 s f => @lem3450992 _89422 _89438 s f h0). Qed.
Lemma lem3450994 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) (h1 : term68 _89422 _89438 s f) : term68 _89422 _89438 s f.
Proof. exact (h1). Qed.
Lemma lem3450995 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) (h1 : term66 _89422 _89438 s f) : term66 _89422 _89438 s f.
Proof. exact (h1). Qed.
Lemma lem3450996 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) (h1 : term66 _89422 _89438 s f) (h2 : term68 _89422 _89438 s f) : term66 _89422 _89438 s f.
Proof. exact (@lem3450994 _89422 _89438 s f h2 (@lem3450995 _89422 _89438 s f h1)). Qed.
Lemma lem3450997 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) (h1 : term66 _89422 _89438 s f) : term69 _89422 _89438 s f.
Proof. exact (fun h0 : term68 _89422 _89438 s f => @lem3450996 _89422 _89438 s f h1 h0). Qed.
Lemma lem3450998 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) (h1 : term68 _89422 _89438 s f) : term68 _89422 _89438 s f.
Proof. exact (h1). Qed.
Lemma lem3450999 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) (h1 : term66 _89422 _89438 s f) (h2 : term68 _89422 _89438 s f) : term66 _89422 _89438 s f.
Proof. exact (@lem3450997 _89422 _89438 s f h1 (@lem3450998 _89422 _89438 s f h2)). Qed.
Lemma lem3451000 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) (h1 : term68 _89422 _89438 s f) : term68 _89422 _89438 s f.
Proof. exact (fun h0 : term66 _89422 _89438 s f => @lem3450999 _89422 _89438 s f h0 h1). Qed.
Lemma lem3451001 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : term70 _89422 _89438 s f.
Proof. exact (fun h0 : term68 _89422 _89438 s f => @lem3451000 _89422 _89438 s f h0). Qed.
Lemma lem3451004 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : term68 _89422 _89438 s f.
Proof. exact (@lem3451001 _89422 _89438 s f (@lem3450993 _89422 _89438 s f)). Qed.
Lemma lem3451005 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : term68 _89422 _89438 s f.
Proof. exact (@lem3451004 _89422 _89438 s f). Qed.
Lemma lem3451015 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3451016 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term66 _89422 _89438 s f) = (term71 _89422 _89438 s f).
Proof. exact (@lem3451015 (term67 _89422 _89438 s f)). Qed.
Lemma lem3451018 (t : Prop) : (term72 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3451019 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term71 _89422 _89438 s f) = (term64 _89422 _89438 s f).
Proof. exact (@lem3451018 (term64 _89422 _89438 s f)). Qed.
Lemma lem3451024 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term66 _89422 _89438 s f) = (term64 _89422 _89438 s f).
Proof. exact (TRANS (@lem3451016 _89422 _89438 s f) (@lem3451019 _89422 _89438 s f)). Qed.
Lemma lem3451175 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) : (term73 _89422 _89438 f) = (term74 _89422 _89438 f).
Proof. exact (fun_ext (fun s : _89438 -> Prop => @lem3451024 _89422 _89438 s f)). Qed.
Lemma lem3451176 {_89438 : Type'} : (@all (_89438 -> Prop)) = (@all (_89438 -> Prop)).
Proof. exact (eq_refl (@all (_89438 -> Prop))). Qed.
Lemma lem3451177 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) : (term75 _89422 _89438 f) = (term76 _89422 _89438 f).
Proof. exact (MK_COMB (@lem3451176 _89438) (@lem3451175 _89422 _89438 f)). Qed.
Lemma lem3451182 {_89422 _89438 : Type'} : (term77 _89422 _89438) = (term78 _89422 _89438).
Proof. exact (fun_ext (fun f : type1470 _89422 _89438 => @lem3451177 _89422 _89438 f)). Qed.
Lemma lem3451183 {_89422 _89438 : Type'} : (@all (_89438 -> _89422 -> Prop)) = (@all (_89438 -> _89422 -> Prop)).
Proof. exact (eq_refl (@all (_89438 -> _89422 -> Prop))). Qed.
Lemma lem3451192 {_89422 _89438 : Type'} : (term79 _89422 _89438) = (term80 _89422 _89438).
Proof. exact (MK_COMB (@lem3451183 _89422 _89438) (@lem3451182 _89422 _89438)). Qed.
Lemma lem3451197 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) : (term81 _89422 _89438 s x f x') = (term81 _89422 _89438 s x f x').
Proof. exact (eq_refl (term81 _89422 _89438 s x f x')). Qed.
Lemma lem3451198 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term82 _89422 _89438 s x f) = (term82 _89422 _89438 s x f).
Proof. exact (fun_ext (fun x' : _89438 => @lem3451197 _89422 _89438 s x f x')). Qed.
Lemma lem3451199 {_89438 : Type'} : (@ex _89438) = (@ex _89438).
Proof. exact (eq_refl (@ex _89438)). Qed.
Lemma lem3451200 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term47 _89422 _89438 s x f) = (term47 _89422 _89438 s x f).
Proof. exact (MK_COMB (@lem3451199 _89438) (@lem3451198 _89422 _89438 s x f)). Qed.
Lemma lem3451201 {_89422 : Type'} (x : _89422) (t : _89422 -> Prop) : (@IN _89422 x t) = (@IN _89422 x t).
Proof. exact (eq_refl (@IN _89422 x t)). Qed.
Lemma lem3451206 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (x : _89438) (s : _89438 -> Prop) : (term83 _89422 _89438 t f x s) = (term83 _89422 _89438 t f x s).
Proof. exact (eq_refl (term83 _89422 _89438 t f x s)). Qed.
Lemma lem3451207 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (s : _89438 -> Prop) : (term84 _89422 _89438 t f s) = (term84 _89422 _89438 t f s).
Proof. exact (fun_ext (fun x : _89438 => @lem3451206 _89422 _89438 t f x s)). Qed.
Lemma lem3451208 {_89438 : Type'} : (@ex _89438) = (@ex _89438).
Proof. exact (eq_refl (@ex _89438)). Qed.
Lemma lem3451209 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (s : _89438 -> Prop) : (term34 _89422 _89438 t f s) = (term34 _89422 _89438 t f s).
Proof. exact (MK_COMB (@lem3451208 _89438) (@lem3451207 _89422 _89438 t f s)). Qed.
Lemma lem3451210 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3451211 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (s : _89438 -> Prop) : (term36 _89422 _89438 t f s) = (term36 _89422 _89438 t f s).
Proof. exact (MK_COMB (@lem3451210) (@lem3451209 _89422 _89438 t f s)). Qed.
Lemma lem3451212 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term38 _89422 _89438 f s x t) = (term38 _89422 _89438 f s x t).
Proof. exact (MK_COMB (@lem3451211 _89422 _89438 t f s) (@lem3451201 _89422 x t)). Qed.
Lemma lem3451213 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term40 _89422 _89438 f s x) = (term40 _89422 _89438 f s x).
Proof. exact (fun_ext (fun t : _89422 -> Prop => @lem3451212 _89422 _89438 f s x t)). Qed.
Lemma lem3451214 {_89422 : Type'} : (@ex (_89422 -> Prop)) = (@ex (_89422 -> Prop)).
Proof. exact (eq_refl (@ex (_89422 -> Prop))). Qed.
Lemma lem3451215 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term41 _89422 _89438 f s x) = (term41 _89422 _89438 f s x).
Proof. exact (MK_COMB (@lem3451214 _89422) (@lem3451213 _89422 _89438 f s x)). Qed.
Lemma lem3451216 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3451217 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term43 _89422 _89438 f s x) = (term43 _89422 _89438 f s x).
Proof. exact (MK_COMB (@lem3451216) (@lem3451215 _89422 _89438 f s x)). Qed.
Lemma lem3451218 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : ((term41 _89422 _89438 f s x) = (term47 _89422 _89438 s x f)) = ((term41 _89422 _89438 f s x) = (term47 _89422 _89438 s x f)).
Proof. exact (MK_COMB (@lem3451217 _89422 _89438 f s x) (@lem3451200 _89422 _89438 s x f)). Qed.
Lemma lem3451219 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term63 _89422 _89438 s f) = (term63 _89422 _89438 s f).
Proof. exact (fun_ext (fun x : _89422 => @lem3451218 _89422 _89438 s x f)). Qed.
Lemma lem3451220 {_89422 : Type'} : (@all _89422) = (@all _89422).
Proof. exact (eq_refl (@all _89422)). Qed.
Lemma lem3451221 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term64 _89422 _89438 s f) = (term64 _89422 _89438 s f).
Proof. exact (MK_COMB (@lem3451220 _89422) (@lem3451219 _89422 _89438 s f)). Qed.
Lemma lem3451222 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) : (term74 _89422 _89438 f) = (term74 _89422 _89438 f).
Proof. exact (fun_ext (fun s : _89438 -> Prop => @lem3451221 _89422 _89438 s f)). Qed.
Lemma lem3451223 {_89438 : Type'} : (@all (_89438 -> Prop)) = (@all (_89438 -> Prop)).
Proof. exact (eq_refl (@all (_89438 -> Prop))). Qed.
Lemma lem3451224 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) : (term76 _89422 _89438 f) = (term76 _89422 _89438 f).
Proof. exact (MK_COMB (@lem3451223 _89438) (@lem3451222 _89422 _89438 f)). Qed.
Lemma lem3451225 {_89422 _89438 : Type'} : (term78 _89422 _89438) = (term78 _89422 _89438).
Proof. exact (fun_ext (fun f : type1470 _89422 _89438 => @lem3451224 _89422 _89438 f)). Qed.
Lemma lem3451226 {_89422 _89438 : Type'} : (@all (_89438 -> _89422 -> Prop)) = (@all (_89438 -> _89422 -> Prop)).
Proof. exact (eq_refl (@all (_89438 -> _89422 -> Prop))). Qed.
Lemma lem3451227 {_89422 _89438 : Type'} : (term80 _89422 _89438) = (term80 _89422 _89438).
Proof. exact (MK_COMB (@lem3451226 _89422 _89438) (@lem3451225 _89422 _89438)). Qed.
Lemma lem3451272 {_89422 _89438 : Type'} : (term79 _89422 _89438) = (term80 _89422 _89438).
Proof. exact (TRANS (@lem3451192 _89422 _89438) (@lem3451227 _89422 _89438)). Qed.
Lemma lem3451273 {_89422 _89438 : Type'} : (term80 _89422 _89438) = (term79 _89422 _89438).
Proof. exact (SYM (@lem3451272 _89422 _89438)). Qed.
Lemma lem3451275 (p : Prop) : p = (term65 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3451276 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : ((term41 _89422 _89438 f s x) = (term47 _89422 _89438 s x f)) = (term85 _89422 _89438 s x f).
Proof. exact (@lem3451275 ((term41 _89422 _89438 f s x) = (term47 _89422 _89438 s x f))). Qed.
Lemma lem3451277 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term85 _89422 _89438 s x f) = ((term41 _89422 _89438 f s x) = (term47 _89422 _89438 s x f)).
Proof. exact (SYM (@lem3451276 _89422 _89438 s x f)). Qed.
Lemma lem3451278 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term86 _89422 _89438 s x f) : term86 _89422 _89438 s x f.
Proof. exact (h1). Qed.
Lemma lem3451287 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (x : _89438) (s : _89438 -> Prop) : (term87 _89422 _89438 t f x s) = (term88 _89422 _89438 t f x s).
Proof. exact (@lem17045 (t = (f x)) (@IN _89438 x s)). Qed.
Lemma lem3451290 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (x : _89438) (s : _89438 -> Prop) : (term83 _89422 _89438 t f x s) = (term83 _89422 _89438 t f x s).
Proof. exact (eq_refl (term83 _89422 _89438 t f x s)). Qed.
Lemma lem3451291 {_89438 : Type'} (P : _89438 -> Prop) : (term89 _89438 P) = (term90 _89438 P).
Proof. exact (@lem18394 _89438 P). Qed.
Lemma lem3451292 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (s : _89438 -> Prop) : (term91 _89422 _89438 t f s) = (term92 _89422 _89438 t f s).
Proof. exact (@lem3451291 _89438 (term84 _89422 _89438 t f s)). Qed.
Lemma lem3451293 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (x : _89438) (s : _89438 -> Prop) : (term93 _89422 _89438 t f s x) = (term83 _89422 _89438 t f x s).
Proof. exact (eq_refl (term93 _89422 _89438 t f s x)). Qed.
Lemma lem3451294 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3451295 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (x : _89438) (s : _89438 -> Prop) : (term94 _89422 _89438 t f s x) = (term87 _89422 _89438 t f x s).
Proof. exact (MK_COMB (@lem3451294) (@lem3451293 _89422 _89438 t f x s)). Qed.
Lemma lem3451296 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (x : _89438) (s : _89438 -> Prop) : (term94 _89422 _89438 t f s x) = (term88 _89422 _89438 t f x s).
Proof. exact (TRANS (@lem3451295 _89422 _89438 t f x s) (@lem3451287 _89422 _89438 t f x s)). Qed.
Lemma lem3451297 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (s : _89438 -> Prop) : (term95 _89422 _89438 t f s) = (term96 _89422 _89438 t f s).
Proof. exact (fun_ext (fun x : _89438 => @lem3451296 _89422 _89438 t f x s)). Qed.
Lemma lem3451298 {_89438 : Type'} : (@all _89438) = (@all _89438).
Proof. exact (eq_refl (@all _89438)). Qed.
Lemma lem3451299 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (s : _89438 -> Prop) : (term92 _89422 _89438 t f s) = (term97 _89422 _89438 t f s).
Proof. exact (MK_COMB (@lem3451298 _89438) (@lem3451297 _89422 _89438 t f s)). Qed.
Lemma lem3451300 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (s : _89438 -> Prop) : (term91 _89422 _89438 t f s) = (term97 _89422 _89438 t f s).
Proof. exact (TRANS (@lem3451292 _89422 _89438 t f s) (@lem3451299 _89422 _89438 t f s)). Qed.
Lemma lem3451301 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (s : _89438 -> Prop) : (term84 _89422 _89438 t f s) = (term84 _89422 _89438 t f s).
Proof. exact (fun_ext (fun x : _89438 => @lem3451290 _89422 _89438 t f x s)). Qed.
Lemma lem3451302 {_89438 : Type'} : (@ex _89438) = (@ex _89438).
Proof. exact (eq_refl (@ex _89438)). Qed.
Lemma lem3451303 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (s : _89438 -> Prop) : (term34 _89422 _89438 t f s) = (term34 _89422 _89438 t f s).
Proof. exact (MK_COMB (@lem3451302 _89438) (@lem3451301 _89422 _89438 t f s)). Qed.
Lemma lem3451304 {_89422 : Type'} (x : _89422) (t : _89422 -> Prop) : (term98 _89422 x t) = (term98 _89422 x t).
Proof. exact (eq_refl (term98 _89422 x t)). Qed.
Lemma lem3451305 {_89422 : Type'} (x : _89422) (t : _89422 -> Prop) : (@IN _89422 x t) = (@IN _89422 x t).
Proof. exact (eq_refl (@IN _89422 x t)). Qed.
Lemma lem3451306 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3451307 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (s : _89438 -> Prop) : (term99 _89422 _89438 t f s) = (term100 _89422 _89438 t f s).
Proof. exact (MK_COMB (@lem3451306) (@lem3451300 _89422 _89438 t f s)). Qed.
Lemma lem3451308 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term101 _89422 _89438 f s x t) = (term102 _89422 _89438 f s x t).
Proof. exact (MK_COMB (@lem3451307 _89422 _89438 t f s) (@lem3451304 _89422 x t)). Qed.
Lemma lem3451309 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term103 _89422 _89438 f s x t) = (term101 _89422 _89438 f s x t).
Proof. exact (@lem17045 (term34 _89422 _89438 t f s) (@IN _89422 x t)). Qed.
Lemma lem3451310 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term103 _89422 _89438 f s x t) = (term102 _89422 _89438 f s x t).
Proof. exact (TRANS (@lem3451309 _89422 _89438 f s x t) (@lem3451308 _89422 _89438 f s x t)). Qed.
Lemma lem3451311 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3451312 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (s : _89438 -> Prop) : (term36 _89422 _89438 t f s) = (term36 _89422 _89438 t f s).
Proof. exact (MK_COMB (@lem3451311) (@lem3451303 _89422 _89438 t f s)). Qed.
Lemma lem3451313 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term38 _89422 _89438 f s x t) = (term38 _89422 _89438 f s x t).
Proof. exact (MK_COMB (@lem3451312 _89422 _89438 t f s) (@lem3451305 _89422 x t)). Qed.
Lemma lem3451314 {_89422 : Type'} (P : type686 _89422) : (term104 _89422 P) = (term105 _89422 P).
Proof. exact (@lem18394 (_89422 -> Prop) P). Qed.
Lemma lem3451315 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term106 _89422 _89438 f s x) = (term107 _89422 _89438 f s x).
Proof. exact (@lem3451314 _89422 (term40 _89422 _89438 f s x)). Qed.
Lemma lem3451316 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term108 _89422 _89438 f s x t) = (term38 _89422 _89438 f s x t).
Proof. exact (eq_refl (term108 _89422 _89438 f s x t)). Qed.
Lemma lem3451317 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3451318 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term109 _89422 _89438 f s x t) = (term103 _89422 _89438 f s x t).
Proof. exact (MK_COMB (@lem3451317) (@lem3451316 _89422 _89438 f s x t)). Qed.
Lemma lem3451319 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term109 _89422 _89438 f s x t) = (term102 _89422 _89438 f s x t).
Proof. exact (TRANS (@lem3451318 _89422 _89438 f s x t) (@lem3451310 _89422 _89438 f s x t)). Qed.
Lemma lem3451320 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term110 _89422 _89438 f s x) = (term111 _89422 _89438 f s x).
Proof. exact (fun_ext (fun t : _89422 -> Prop => @lem3451319 _89422 _89438 f s x t)). Qed.
Lemma lem3451321 {_89422 : Type'} : (@all (_89422 -> Prop)) = (@all (_89422 -> Prop)).
Proof. exact (eq_refl (@all (_89422 -> Prop))). Qed.
Lemma lem3451322 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term107 _89422 _89438 f s x) = (term112 _89422 _89438 f s x).
Proof. exact (MK_COMB (@lem3451321 _89422) (@lem3451320 _89422 _89438 f s x)). Qed.
Lemma lem3451323 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term106 _89422 _89438 f s x) = (term112 _89422 _89438 f s x).
Proof. exact (TRANS (@lem3451315 _89422 _89438 f s x) (@lem3451322 _89422 _89438 f s x)). Qed.
Lemma lem3451324 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term40 _89422 _89438 f s x) = (term40 _89422 _89438 f s x).
Proof. exact (fun_ext (fun t : _89422 -> Prop => @lem3451313 _89422 _89438 f s x t)). Qed.
Lemma lem3451325 {_89422 : Type'} : (@ex (_89422 -> Prop)) = (@ex (_89422 -> Prop)).
Proof. exact (eq_refl (@ex (_89422 -> Prop))). Qed.
Lemma lem3451326 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term41 _89422 _89438 f s x) = (term41 _89422 _89438 f s x).
Proof. exact (MK_COMB (@lem3451325 _89422) (@lem3451324 _89422 _89438 f s x)). Qed.
Lemma lem3451335 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) : (term113 _89422 _89438 s x f x') = (term114 _89422 _89438 s x f x').
Proof. exact (@lem17045 (@IN _89438 x' s) (term115 _89422 _89438 x f x')). Qed.
Lemma lem3451338 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) : (term81 _89422 _89438 s x f x') = (term81 _89422 _89438 s x f x').
Proof. exact (eq_refl (term81 _89422 _89438 s x f x')). Qed.
Lemma lem3451339 {_89438 : Type'} (P : _89438 -> Prop) : (term89 _89438 P) = (term90 _89438 P).
Proof. exact (@lem18394 _89438 P). Qed.
Lemma lem3451340 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term116 _89422 _89438 s x f) = (term117 _89422 _89438 s x f).
Proof. exact (@lem3451339 _89438 (term82 _89422 _89438 s x f)). Qed.
Lemma lem3451341 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) : (term118 _89422 _89438 s x f x') = (term81 _89422 _89438 s x f x').
Proof. exact (eq_refl (term118 _89422 _89438 s x f x')). Qed.
Lemma lem3451342 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3451343 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) : (term119 _89422 _89438 s x f x') = (term113 _89422 _89438 s x f x').
Proof. exact (MK_COMB (@lem3451342) (@lem3451341 _89422 _89438 s x f x')). Qed.
Lemma lem3451344 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) : (term119 _89422 _89438 s x f x') = (term114 _89422 _89438 s x f x').
Proof. exact (TRANS (@lem3451343 _89422 _89438 s x f x') (@lem3451335 _89422 _89438 s x f x')). Qed.
Lemma lem3451345 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term120 _89422 _89438 s x f) = (term121 _89422 _89438 s x f).
Proof. exact (fun_ext (fun x' : _89438 => @lem3451344 _89422 _89438 s x f x')). Qed.
Lemma lem3451346 {_89438 : Type'} : (@all _89438) = (@all _89438).
Proof. exact (eq_refl (@all _89438)). Qed.
Lemma lem3451347 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term117 _89422 _89438 s x f) = (term122 _89422 _89438 s x f).
Proof. exact (MK_COMB (@lem3451346 _89438) (@lem3451345 _89422 _89438 s x f)). Qed.
Lemma lem3451348 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term116 _89422 _89438 s x f) = (term122 _89422 _89438 s x f).
Proof. exact (TRANS (@lem3451340 _89422 _89438 s x f) (@lem3451347 _89422 _89438 s x f)). Qed.
Lemma lem3451349 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term82 _89422 _89438 s x f) = (term82 _89422 _89438 s x f).
Proof. exact (fun_ext (fun x' : _89438 => @lem3451338 _89422 _89438 s x f x')). Qed.
Lemma lem3451350 {_89438 : Type'} : (@ex _89438) = (@ex _89438).
Proof. exact (eq_refl (@ex _89438)). Qed.
Lemma lem3451351 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term47 _89422 _89438 s x f) = (term47 _89422 _89438 s x f).
Proof. exact (MK_COMB (@lem3451350 _89438) (@lem3451349 _89422 _89438 s x f)). Qed.
Lemma lem3451352 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3451353 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term123 _89422 _89438 f s x) = (term124 _89422 _89438 f s x).
Proof. exact (MK_COMB (@lem3451352) (@lem3451323 _89422 _89438 f s x)). Qed.
Lemma lem3451354 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term125 _89422 _89438 s x f) = (term126 _89422 _89438 s x f).
Proof. exact (MK_COMB (@lem3451353 _89422 _89438 f s x) (@lem3451351 _89422 _89438 s x f)). Qed.
Lemma lem3451355 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3451356 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term127 _89422 _89438 f s x) = (term127 _89422 _89438 f s x).
Proof. exact (MK_COMB (@lem3451355) (@lem3451326 _89422 _89438 f s x)). Qed.
Lemma lem3451357 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term128 _89422 _89438 s x f) = (term129 _89422 _89438 s x f).
Proof. exact (MK_COMB (@lem3451356 _89422 _89438 f s x) (@lem3451348 _89422 _89438 s x f)). Qed.
Lemma lem3451358 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3451359 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term130 _89422 _89438 s x f) = (term131 _89422 _89438 s x f).
Proof. exact (MK_COMB (@lem3451358) (@lem3451357 _89422 _89438 s x f)). Qed.
Lemma lem3451360 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term132 _89422 _89438 s x f) = (term133 _89422 _89438 s x f).
Proof. exact (MK_COMB (@lem3451359 _89422 _89438 s x f) (@lem3451354 _89422 _89438 s x f)). Qed.
Lemma lem3451361 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term86 _89422 _89438 s x f) = (term132 _89422 _89438 s x f).
Proof. exact (@lem17646 (term41 _89422 _89438 f s x) (term47 _89422 _89438 s x f)). Qed.
Lemma lem3451362 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term86 _89422 _89438 s x f) = (term133 _89422 _89438 s x f).
Proof. exact (TRANS (@lem3451361 _89422 _89438 s x f) (@lem3451360 _89422 _89438 s x f)). Qed.
Lemma lem3451653 {A : Type'} (P : A -> Prop) (Q : Prop) : (term134 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3451654 {_89438 : Type'} (P : _89438 -> Prop) (Q : Prop) : (term134 _89438 P Q) = (term135 _89438 P Q).
Proof. exact (@lem3451653 _89438 P Q). Qed.
Lemma lem3451655 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term136 _89422 _89438 f s x t) = (term137 _89422 _89438 f s x t).
Proof. exact (@lem3451654 _89438 (term84 _89422 _89438 t f s) (@IN _89422 x t)). Qed.
Lemma lem3451656 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (x : _89438) (s : _89438 -> Prop) : (term93 _89422 _89438 t f s x) = (term83 _89422 _89438 t f x s).
Proof. exact (eq_refl (term93 _89422 _89438 t f s x)). Qed.
Lemma lem3451657 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (s : _89438 -> Prop) : (term138 _89422 _89438 t f s) = (term84 _89422 _89438 t f s).
Proof. exact (fun_ext (fun x : _89438 => @lem3451656 _89422 _89438 t f x s)). Qed.
Lemma lem3451658 {_89438 : Type'} : (@ex _89438) = (@ex _89438).
Proof. exact (eq_refl (@ex _89438)). Qed.
Lemma lem3451659 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (s : _89438 -> Prop) : (term139 _89422 _89438 t f s) = (term34 _89422 _89438 t f s).
Proof. exact (MK_COMB (@lem3451658 _89438) (@lem3451657 _89422 _89438 t f s)). Qed.
Lemma lem3451660 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3451661 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (s : _89438 -> Prop) : (term140 _89422 _89438 t f s) = (term36 _89422 _89438 t f s).
Proof. exact (MK_COMB (@lem3451660) (@lem3451659 _89422 _89438 t f s)). Qed.
Lemma lem3451662 {_89422 : Type'} (x : _89422) (t : _89422 -> Prop) : (@IN _89422 x t) = (@IN _89422 x t).
Proof. exact (eq_refl (@IN _89422 x t)). Qed.
Lemma lem3451663 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term136 _89422 _89438 f s x t) = (term38 _89422 _89438 f s x t).
Proof. exact (MK_COMB (@lem3451661 _89422 _89438 t f s) (@lem3451662 _89422 x t)). Qed.
Lemma lem3451664 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3451665 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term141 _89422 _89438 f s x t) = (term142 _89422 _89438 f s x t).
Proof. exact (MK_COMB (@lem3451664) (@lem3451663 _89422 _89438 f s x t)). Qed.
Lemma lem3451666 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (x : _89438) (s : _89438 -> Prop) : (term93 _89422 _89438 t f s x) = (term83 _89422 _89438 t f x s).
Proof. exact (eq_refl (term93 _89422 _89438 t f s x)). Qed.
Lemma lem3451667 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3451668 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (x : _89438) (s : _89438 -> Prop) : (term143 _89422 _89438 t f s x) = (term144 _89422 _89438 t f x s).
Proof. exact (MK_COMB (@lem3451667) (@lem3451666 _89422 _89438 t f x s)). Qed.
Lemma lem3451669 {_89422 : Type'} (x : _89422) (t : _89422 -> Prop) : (@IN _89422 x t) = (@IN _89422 x t).
Proof. exact (eq_refl (@IN _89422 x t)). Qed.
Lemma lem3451670 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (x : _89438) (s : _89438 -> Prop) (x' : _89422) (t : _89422 -> Prop) : (term145 _89422 _89438 f s x x' t) = (term146 _89422 _89438 f x s x' t).
Proof. exact (MK_COMB (@lem3451668 _89422 _89438 t f x s) (@lem3451669 _89422 x' t)). Qed.
Lemma lem3451671 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term147 _89422 _89438 f s x t) = (term148 _89422 _89438 f s x t).
Proof. exact (fun_ext (fun x' : _89438 => @lem3451670 _89422 _89438 f x' s x t)). Qed.
Lemma lem3451672 {_89438 : Type'} : (@ex _89438) = (@ex _89438).
Proof. exact (eq_refl (@ex _89438)). Qed.
Lemma lem3451673 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term137 _89422 _89438 f s x t) = (term149 _89422 _89438 f s x t).
Proof. exact (MK_COMB (@lem3451672 _89438) (@lem3451671 _89422 _89438 f s x t)). Qed.
Lemma lem3451674 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : ((term136 _89422 _89438 f s x t) = (term137 _89422 _89438 f s x t)) = ((term38 _89422 _89438 f s x t) = (term149 _89422 _89438 f s x t)).
Proof. exact (MK_COMB (@lem3451665 _89422 _89438 f s x t) (@lem3451673 _89422 _89438 f s x t)). Qed.
Lemma lem3451675 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term38 _89422 _89438 f s x t) = (term149 _89422 _89438 f s x t).
Proof. exact (EQ_MP (@lem3451674 _89422 _89438 f s x t) (@lem3451655 _89422 _89438 f s x t)). Qed.
Lemma lem3451676 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term40 _89422 _89438 f s x) = (term150 _89422 _89438 f s x).
Proof. exact (fun_ext (fun t : _89422 -> Prop => @lem3451675 _89422 _89438 f s x t)). Qed.
Lemma lem3451677 {_89422 : Type'} : (@ex (_89422 -> Prop)) = (@ex (_89422 -> Prop)).
Proof. exact (eq_refl (@ex (_89422 -> Prop))). Qed.
Lemma lem3451678 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term41 _89422 _89438 f s x) = (term151 _89422 _89438 f s x).
Proof. exact (MK_COMB (@lem3451677 _89422) (@lem3451676 _89422 _89438 f s x)). Qed.
Lemma lem3451679 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3451680 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term127 _89422 _89438 f s x) = (term152 _89422 _89438 f s x).
Proof. exact (MK_COMB (@lem3451679) (@lem3451678 _89422 _89438 f s x)). Qed.
Lemma lem3451681 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term122 _89422 _89438 s x f) = (term122 _89422 _89438 s x f).
Proof. exact (eq_refl (term122 _89422 _89438 s x f)). Qed.
Lemma lem3451682 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term129 _89422 _89438 s x f) = (term153 _89422 _89438 s x f).
Proof. exact (MK_COMB (@lem3451680 _89422 _89438 f s x) (@lem3451681 _89422 _89438 s x f)). Qed.
Lemma lem3451684 {A : Type'} (P : A -> Prop) (Q : Prop) : (term134 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3451685 {_89422 : Type'} (P : type686 _89422) (Q : Prop) : (term154 _89422 P Q) = (term155 _89422 P Q).
Proof. exact (@lem3451684 (_89422 -> Prop) P Q). Qed.
Lemma lem3451686 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term156 _89422 _89438 s x f) = (term157 _89422 _89438 s x f).
Proof. exact (@lem3451685 _89422 (term150 _89422 _89438 f s x) (term122 _89422 _89438 s x f)). Qed.
Lemma lem3451687 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term158 _89422 _89438 f s x t) = (term149 _89422 _89438 f s x t).
Proof. exact (eq_refl (term158 _89422 _89438 f s x t)). Qed.
Lemma lem3451688 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term159 _89422 _89438 f s x) = (term150 _89422 _89438 f s x).
Proof. exact (fun_ext (fun t : _89422 -> Prop => @lem3451687 _89422 _89438 f s x t)). Qed.
Lemma lem3451689 {_89422 : Type'} : (@ex (_89422 -> Prop)) = (@ex (_89422 -> Prop)).
Proof. exact (eq_refl (@ex (_89422 -> Prop))). Qed.
Lemma lem3451690 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term160 _89422 _89438 f s x) = (term151 _89422 _89438 f s x).
Proof. exact (MK_COMB (@lem3451689 _89422) (@lem3451688 _89422 _89438 f s x)). Qed.
Lemma lem3451691 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3451692 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term161 _89422 _89438 f s x) = (term152 _89422 _89438 f s x).
Proof. exact (MK_COMB (@lem3451691) (@lem3451690 _89422 _89438 f s x)). Qed.
Lemma lem3451693 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term122 _89422 _89438 s x f) = (term122 _89422 _89438 s x f).
Proof. exact (eq_refl (term122 _89422 _89438 s x f)). Qed.
Lemma lem3451694 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term156 _89422 _89438 s x f) = (term153 _89422 _89438 s x f).
Proof. exact (MK_COMB (@lem3451692 _89422 _89438 f s x) (@lem3451693 _89422 _89438 s x f)). Qed.
Lemma lem3451695 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3451696 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term162 _89422 _89438 s x f) = (term163 _89422 _89438 s x f).
Proof. exact (MK_COMB (@lem3451695) (@lem3451694 _89422 _89438 s x f)). Qed.
Lemma lem3451697 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term158 _89422 _89438 f s x t) = (term149 _89422 _89438 f s x t).
Proof. exact (eq_refl (term158 _89422 _89438 f s x t)). Qed.
Lemma lem3451698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3451699 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term164 _89422 _89438 f s x t) = (term165 _89422 _89438 f s x t).
Proof. exact (MK_COMB (@lem3451698) (@lem3451697 _89422 _89438 f s x t)). Qed.
Lemma lem3451700 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term122 _89422 _89438 s x f) = (term122 _89422 _89438 s x f).
Proof. exact (eq_refl (term122 _89422 _89438 s x f)). Qed.
Lemma lem3451701 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term166 _89422 _89438 t s x f) = (term167 _89422 _89438 t s x f).
Proof. exact (MK_COMB (@lem3451699 _89422 _89438 f s x t) (@lem3451700 _89422 _89438 s x f)). Qed.
Lemma lem3451702 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term168 _89422 _89438 s x f) = (term169 _89422 _89438 s x f).
Proof. exact (fun_ext (fun t : _89422 -> Prop => @lem3451701 _89422 _89438 t s x f)). Qed.
Lemma lem3451703 {_89422 : Type'} : (@ex (_89422 -> Prop)) = (@ex (_89422 -> Prop)).
Proof. exact (eq_refl (@ex (_89422 -> Prop))). Qed.
Lemma lem3451704 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term157 _89422 _89438 s x f) = (term170 _89422 _89438 s x f).
Proof. exact (MK_COMB (@lem3451703 _89422) (@lem3451702 _89422 _89438 s x f)). Qed.
Lemma lem3451705 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : ((term156 _89422 _89438 s x f) = (term157 _89422 _89438 s x f)) = ((term153 _89422 _89438 s x f) = (term170 _89422 _89438 s x f)).
Proof. exact (MK_COMB (@lem3451696 _89422 _89438 s x f) (@lem3451704 _89422 _89438 s x f)). Qed.
Lemma lem3451706 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term153 _89422 _89438 s x f) = (term170 _89422 _89438 s x f).
Proof. exact (EQ_MP (@lem3451705 _89422 _89438 s x f) (@lem3451686 _89422 _89438 s x f)). Qed.
Lemma lem3451708 {A : Type'} (P : A -> Prop) (Q : Prop) : (term134 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3451709 {_89438 : Type'} (P : _89438 -> Prop) (Q : Prop) : (term134 _89438 P Q) = (term135 _89438 P Q).
Proof. exact (@lem3451708 _89438 P Q). Qed.
Lemma lem3451710 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term171 _89422 _89438 t s x f) = (term172 _89422 _89438 t s x f).
Proof. exact (@lem3451709 _89438 (term148 _89422 _89438 f s x t) (term122 _89422 _89438 s x f)). Qed.
Lemma lem3451711 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (x : _89438) (s : _89438 -> Prop) (x' : _89422) (t : _89422 -> Prop) : (term173 _89422 _89438 f s x' t x) = (term146 _89422 _89438 f x s x' t).
Proof. exact (eq_refl (term173 _89422 _89438 f s x' t x)). Qed.
Lemma lem3451712 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term174 _89422 _89438 f s x t) = (term148 _89422 _89438 f s x t).
Proof. exact (fun_ext (fun x' : _89438 => @lem3451711 _89422 _89438 f x' s x t)). Qed.
Lemma lem3451713 {_89438 : Type'} : (@ex _89438) = (@ex _89438).
Proof. exact (eq_refl (@ex _89438)). Qed.
Lemma lem3451714 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term175 _89422 _89438 f s x t) = (term149 _89422 _89438 f s x t).
Proof. exact (MK_COMB (@lem3451713 _89438) (@lem3451712 _89422 _89438 f s x t)). Qed.
Lemma lem3451715 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3451716 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term176 _89422 _89438 f s x t) = (term165 _89422 _89438 f s x t).
Proof. exact (MK_COMB (@lem3451715) (@lem3451714 _89422 _89438 f s x t)). Qed.
Lemma lem3451717 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term122 _89422 _89438 s x f) = (term122 _89422 _89438 s x f).
Proof. exact (eq_refl (term122 _89422 _89438 s x f)). Qed.
Lemma lem3451718 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term171 _89422 _89438 t s x f) = (term167 _89422 _89438 t s x f).
Proof. exact (MK_COMB (@lem3451716 _89422 _89438 f s x t) (@lem3451717 _89422 _89438 s x f)). Qed.
Lemma lem3451719 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3451720 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term177 _89422 _89438 t s x f) = (term178 _89422 _89438 t s x f).
Proof. exact (MK_COMB (@lem3451719) (@lem3451718 _89422 _89438 t s x f)). Qed.
Lemma lem3451721 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (x : _89438) (s : _89438 -> Prop) (x' : _89422) (t : _89422 -> Prop) : (term173 _89422 _89438 f s x' t x) = (term146 _89422 _89438 f x s x' t).
Proof. exact (eq_refl (term173 _89422 _89438 f s x' t x)). Qed.
Lemma lem3451722 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3451723 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (x : _89438) (s : _89438 -> Prop) (x' : _89422) (t : _89422 -> Prop) : (term179 _89422 _89438 f s x' t x) = (term180 _89422 _89438 f x s x' t).
Proof. exact (MK_COMB (@lem3451722) (@lem3451721 _89422 _89438 f x s x' t)). Qed.
Lemma lem3451724 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term122 _89422 _89438 s x f) = (term122 _89422 _89438 s x f).
Proof. exact (eq_refl (term122 _89422 _89438 s x f)). Qed.
Lemma lem3451725 {_89422 _89438 : Type'} (x : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x' : _89422) (f : type1470 _89422 _89438) : (term181 _89422 _89438 t x s x' f) = (term182 _89422 _89438 x t s x' f).
Proof. exact (MK_COMB (@lem3451723 _89422 _89438 f x s x' t) (@lem3451724 _89422 _89438 s x' f)). Qed.
Lemma lem3451726 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term183 _89422 _89438 t s x f) = (term184 _89422 _89438 t s x f).
Proof. exact (fun_ext (fun x' : _89438 => @lem3451725 _89422 _89438 x' t s x f)). Qed.
Lemma lem3451727 {_89438 : Type'} : (@ex _89438) = (@ex _89438).
Proof. exact (eq_refl (@ex _89438)). Qed.
Lemma lem3451728 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term172 _89422 _89438 t s x f) = (term185 _89422 _89438 t s x f).
Proof. exact (MK_COMB (@lem3451727 _89438) (@lem3451726 _89422 _89438 t s x f)). Qed.
Lemma lem3451729 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : ((term171 _89422 _89438 t s x f) = (term172 _89422 _89438 t s x f)) = ((term167 _89422 _89438 t s x f) = (term185 _89422 _89438 t s x f)).
Proof. exact (MK_COMB (@lem3451720 _89422 _89438 t s x f) (@lem3451728 _89422 _89438 t s x f)). Qed.
Lemma lem3451730 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term167 _89422 _89438 t s x f) = (term185 _89422 _89438 t s x f).
Proof. exact (EQ_MP (@lem3451729 _89422 _89438 t s x f) (@lem3451710 _89422 _89438 t s x f)). Qed.
Lemma lem3451731 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term169 _89422 _89438 s x f) = (term186 _89422 _89438 s x f).
Proof. exact (fun_ext (fun t : _89422 -> Prop => @lem3451730 _89422 _89438 t s x f)). Qed.
Lemma lem3451732 {_89422 : Type'} : (@ex (_89422 -> Prop)) = (@ex (_89422 -> Prop)).
Proof. exact (eq_refl (@ex (_89422 -> Prop))). Qed.
Lemma lem3451733 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term170 _89422 _89438 s x f) = (term187 _89422 _89438 s x f).
Proof. exact (MK_COMB (@lem3451732 _89422) (@lem3451731 _89422 _89438 s x f)). Qed.
Lemma lem3451734 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term153 _89422 _89438 s x f) = (term187 _89422 _89438 s x f).
Proof. exact (TRANS (@lem3451706 _89422 _89438 s x f) (@lem3451733 _89422 _89438 s x f)). Qed.
Lemma lem3451735 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term129 _89422 _89438 s x f) = (term187 _89422 _89438 s x f).
Proof. exact (TRANS (@lem3451682 _89422 _89438 s x f) (@lem3451734 _89422 _89438 s x f)). Qed.
Lemma lem3451736 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3451737 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term131 _89422 _89438 s x f) = (term188 _89422 _89438 s x f).
Proof. exact (MK_COMB (@lem3451736) (@lem3451735 _89422 _89438 s x f)). Qed.
Lemma lem3451739 {A : Type'} (P : Prop) (Q : A -> Prop) : (term189 A P Q) = (term190 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3451740 {_89438 : Type'} (P : Prop) (Q : _89438 -> Prop) : (term189 _89438 P Q) = (term190 _89438 P Q).
Proof. exact (@lem3451739 _89438 P Q). Qed.
Lemma lem3451741 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term191 _89422 _89438 s x f) = (term192 _89422 _89438 s x f).
Proof. exact (@lem3451740 _89438 (term112 _89422 _89438 f s x) (term82 _89422 _89438 s x f)). Qed.
Lemma lem3451742 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) : (term118 _89422 _89438 s x f x') = (term81 _89422 _89438 s x f x').
Proof. exact (eq_refl (term118 _89422 _89438 s x f x')). Qed.
Lemma lem3451743 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term193 _89422 _89438 s x f) = (term82 _89422 _89438 s x f).
Proof. exact (fun_ext (fun x' : _89438 => @lem3451742 _89422 _89438 s x f x')). Qed.
Lemma lem3451744 {_89438 : Type'} : (@ex _89438) = (@ex _89438).
Proof. exact (eq_refl (@ex _89438)). Qed.
Lemma lem3451745 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term194 _89422 _89438 s x f) = (term47 _89422 _89438 s x f).
Proof. exact (MK_COMB (@lem3451744 _89438) (@lem3451743 _89422 _89438 s x f)). Qed.
Lemma lem3451746 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term124 _89422 _89438 f s x) = (term124 _89422 _89438 f s x).
Proof. exact (eq_refl (term124 _89422 _89438 f s x)). Qed.
Lemma lem3451747 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term191 _89422 _89438 s x f) = (term126 _89422 _89438 s x f).
Proof. exact (MK_COMB (@lem3451746 _89422 _89438 f s x) (@lem3451745 _89422 _89438 s x f)). Qed.
Lemma lem3451748 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3451749 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term195 _89422 _89438 s x f) = (term196 _89422 _89438 s x f).
Proof. exact (MK_COMB (@lem3451748) (@lem3451747 _89422 _89438 s x f)). Qed.
Lemma lem3451750 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) : (term118 _89422 _89438 s x f x') = (term81 _89422 _89438 s x f x').
Proof. exact (eq_refl (term118 _89422 _89438 s x f x')). Qed.
Lemma lem3451751 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term124 _89422 _89438 f s x) = (term124 _89422 _89438 f s x).
Proof. exact (eq_refl (term124 _89422 _89438 f s x)). Qed.
Lemma lem3451752 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) : (term197 _89422 _89438 s x f x') = (term198 _89422 _89438 s x f x').
Proof. exact (MK_COMB (@lem3451751 _89422 _89438 f s x) (@lem3451750 _89422 _89438 s x f x')). Qed.
Lemma lem3451753 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term199 _89422 _89438 s x f) = (term200 _89422 _89438 s x f).
Proof. exact (fun_ext (fun x' : _89438 => @lem3451752 _89422 _89438 s x f x')). Qed.
Lemma lem3451754 {_89438 : Type'} : (@ex _89438) = (@ex _89438).
Proof. exact (eq_refl (@ex _89438)). Qed.
Lemma lem3451755 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term192 _89422 _89438 s x f) = (term201 _89422 _89438 s x f).
Proof. exact (MK_COMB (@lem3451754 _89438) (@lem3451753 _89422 _89438 s x f)). Qed.
Lemma lem3451756 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : ((term191 _89422 _89438 s x f) = (term192 _89422 _89438 s x f)) = ((term126 _89422 _89438 s x f) = (term201 _89422 _89438 s x f)).
Proof. exact (MK_COMB (@lem3451749 _89422 _89438 s x f) (@lem3451755 _89422 _89438 s x f)). Qed.
Lemma lem3451757 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term126 _89422 _89438 s x f) = (term201 _89422 _89438 s x f).
Proof. exact (EQ_MP (@lem3451756 _89422 _89438 s x f) (@lem3451741 _89422 _89438 s x f)). Qed.
Lemma lem3451758 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term133 _89422 _89438 s x f) = (term202 _89422 _89438 s x f).
Proof. exact (MK_COMB (@lem3451737 _89422 _89438 s x f) (@lem3451757 _89422 _89438 s x f)). Qed.
Lemma lem3451762 {A : Type'} (P : A -> Prop) (Q : Prop) : (term203 A P Q) = (term204 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3451763 {_89422 : Type'} (P : type686 _89422) (Q : Prop) : (term205 _89422 P Q) = (term206 _89422 P Q).
Proof. exact (@lem3451762 (_89422 -> Prop) P Q). Qed.
Lemma lem3451764 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term207 _89422 _89438 s x f) = (term208 _89422 _89438 s x f).
Proof. exact (@lem3451763 _89422 (term186 _89422 _89438 s x f) (term201 _89422 _89438 s x f)). Qed.
Lemma lem3451765 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term209 _89422 _89438 s x f t) = (term185 _89422 _89438 t s x f).
Proof. exact (eq_refl (term209 _89422 _89438 s x f t)). Qed.
Lemma lem3451766 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term210 _89422 _89438 s x f) = (term186 _89422 _89438 s x f).
Proof. exact (fun_ext (fun t : _89422 -> Prop => @lem3451765 _89422 _89438 t s x f)). Qed.
Lemma lem3451767 {_89422 : Type'} : (@ex (_89422 -> Prop)) = (@ex (_89422 -> Prop)).
Proof. exact (eq_refl (@ex (_89422 -> Prop))). Qed.
Lemma lem3451768 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term211 _89422 _89438 s x f) = (term187 _89422 _89438 s x f).
Proof. exact (MK_COMB (@lem3451767 _89422) (@lem3451766 _89422 _89438 s x f)). Qed.
Lemma lem3451769 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3451770 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term212 _89422 _89438 s x f) = (term188 _89422 _89438 s x f).
Proof. exact (MK_COMB (@lem3451769) (@lem3451768 _89422 _89438 s x f)). Qed.
Lemma lem3451771 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term201 _89422 _89438 s x f) = (term201 _89422 _89438 s x f).
Proof. exact (eq_refl (term201 _89422 _89438 s x f)). Qed.
Lemma lem3451772 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term207 _89422 _89438 s x f) = (term202 _89422 _89438 s x f).
Proof. exact (MK_COMB (@lem3451770 _89422 _89438 s x f) (@lem3451771 _89422 _89438 s x f)). Qed.
Lemma lem3451773 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3451774 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term213 _89422 _89438 s x f) = (term214 _89422 _89438 s x f).
Proof. exact (MK_COMB (@lem3451773) (@lem3451772 _89422 _89438 s x f)). Qed.
Lemma lem3451775 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term209 _89422 _89438 s x f t) = (term185 _89422 _89438 t s x f).
Proof. exact (eq_refl (term209 _89422 _89438 s x f t)). Qed.
Lemma lem3451776 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3451777 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term215 _89422 _89438 s x f t) = (term216 _89422 _89438 t s x f).
Proof. exact (MK_COMB (@lem3451776) (@lem3451775 _89422 _89438 t s x f)). Qed.
Lemma lem3451778 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term201 _89422 _89438 s x f) = (term201 _89422 _89438 s x f).
Proof. exact (eq_refl (term201 _89422 _89438 s x f)). Qed.
Lemma lem3451779 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term217 _89422 _89438 t s x f) = (term218 _89422 _89438 t s x f).
Proof. exact (MK_COMB (@lem3451777 _89422 _89438 t s x f) (@lem3451778 _89422 _89438 s x f)). Qed.
Lemma lem3451780 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term219 _89422 _89438 s x f) = (term220 _89422 _89438 s x f).
Proof. exact (fun_ext (fun t : _89422 -> Prop => @lem3451779 _89422 _89438 t s x f)). Qed.
Lemma lem3451781 {_89422 : Type'} : (@ex (_89422 -> Prop)) = (@ex (_89422 -> Prop)).
Proof. exact (eq_refl (@ex (_89422 -> Prop))). Qed.
Lemma lem3451782 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term208 _89422 _89438 s x f) = (term221 _89422 _89438 s x f).
Proof. exact (MK_COMB (@lem3451781 _89422) (@lem3451780 _89422 _89438 s x f)). Qed.
Lemma lem3451783 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : ((term207 _89422 _89438 s x f) = (term208 _89422 _89438 s x f)) = ((term202 _89422 _89438 s x f) = (term221 _89422 _89438 s x f)).
Proof. exact (MK_COMB (@lem3451774 _89422 _89438 s x f) (@lem3451782 _89422 _89438 s x f)). Qed.
Lemma lem3451784 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term202 _89422 _89438 s x f) = (term221 _89422 _89438 s x f).
Proof. exact (EQ_MP (@lem3451783 _89422 _89438 s x f) (@lem3451764 _89422 _89438 s x f)). Qed.
Lemma lem3451786 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term222 A P Q) = (term223 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3451787 {_89438 : Type'} (P : _89438 -> Prop) (Q : _89438 -> Prop) : (term222 _89438 P Q) = (term223 _89438 P Q).
Proof. exact (@lem3451786 _89438 P Q). Qed.
Lemma lem3451788 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term224 _89422 _89438 t s x f) = (term225 _89422 _89438 t s x f).
Proof. exact (@lem3451787 _89438 (term184 _89422 _89438 t s x f) (term200 _89422 _89438 s x f)). Qed.
Lemma lem3451789 {_89422 _89438 : Type'} (x : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x' : _89422) (f : type1470 _89422 _89438) : (term226 _89422 _89438 t s x' f x) = (term182 _89422 _89438 x t s x' f).
Proof. exact (eq_refl (term226 _89422 _89438 t s x' f x)). Qed.
Lemma lem3451790 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term227 _89422 _89438 t s x f) = (term184 _89422 _89438 t s x f).
Proof. exact (fun_ext (fun x' : _89438 => @lem3451789 _89422 _89438 x' t s x f)). Qed.
Lemma lem3451791 {_89438 : Type'} : (@ex _89438) = (@ex _89438).
Proof. exact (eq_refl (@ex _89438)). Qed.
Lemma lem3451792 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term228 _89422 _89438 t s x f) = (term185 _89422 _89438 t s x f).
Proof. exact (MK_COMB (@lem3451791 _89438) (@lem3451790 _89422 _89438 t s x f)). Qed.
Lemma lem3451793 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3451794 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term229 _89422 _89438 t s x f) = (term216 _89422 _89438 t s x f).
Proof. exact (MK_COMB (@lem3451793) (@lem3451792 _89422 _89438 t s x f)). Qed.
Lemma lem3451795 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) : (term230 _89422 _89438 s x f x') = (term198 _89422 _89438 s x f x').
Proof. exact (eq_refl (term230 _89422 _89438 s x f x')). Qed.
Lemma lem3451796 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term231 _89422 _89438 s x f) = (term200 _89422 _89438 s x f).
Proof. exact (fun_ext (fun x' : _89438 => @lem3451795 _89422 _89438 s x f x')). Qed.
Lemma lem3451797 {_89438 : Type'} : (@ex _89438) = (@ex _89438).
Proof. exact (eq_refl (@ex _89438)). Qed.
Lemma lem3451798 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term232 _89422 _89438 s x f) = (term201 _89422 _89438 s x f).
Proof. exact (MK_COMB (@lem3451797 _89438) (@lem3451796 _89422 _89438 s x f)). Qed.
Lemma lem3451799 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term224 _89422 _89438 t s x f) = (term218 _89422 _89438 t s x f).
Proof. exact (MK_COMB (@lem3451794 _89422 _89438 t s x f) (@lem3451798 _89422 _89438 s x f)). Qed.
Lemma lem3451800 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3451801 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term233 _89422 _89438 t s x f) = (term234 _89422 _89438 t s x f).
Proof. exact (MK_COMB (@lem3451800) (@lem3451799 _89422 _89438 t s x f)). Qed.
Lemma lem3451802 {_89422 _89438 : Type'} (x : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x' : _89422) (f : type1470 _89422 _89438) : (term226 _89422 _89438 t s x' f x) = (term182 _89422 _89438 x t s x' f).
Proof. exact (eq_refl (term226 _89422 _89438 t s x' f x)). Qed.
Lemma lem3451803 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3451804 {_89422 _89438 : Type'} (x : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x' : _89422) (f : type1470 _89422 _89438) : (term235 _89422 _89438 t s x' f x) = (term236 _89422 _89438 x t s x' f).
Proof. exact (MK_COMB (@lem3451803) (@lem3451802 _89422 _89438 x t s x' f)). Qed.
Lemma lem3451805 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) : (term230 _89422 _89438 s x f x') = (term198 _89422 _89438 s x f x').
Proof. exact (eq_refl (term230 _89422 _89438 s x f x')). Qed.
Lemma lem3451806 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) : (term237 _89422 _89438 t s x f x') = (term238 _89422 _89438 t s x f x').
Proof. exact (MK_COMB (@lem3451804 _89422 _89438 x' t s x f) (@lem3451805 _89422 _89438 s x f x')). Qed.
Lemma lem3451807 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term239 _89422 _89438 t s x f) = (term240 _89422 _89438 t s x f).
Proof. exact (fun_ext (fun x' : _89438 => @lem3451806 _89422 _89438 t s x f x')). Qed.
Lemma lem3451808 {_89438 : Type'} : (@ex _89438) = (@ex _89438).
Proof. exact (eq_refl (@ex _89438)). Qed.
Lemma lem3451809 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term225 _89422 _89438 t s x f) = (term241 _89422 _89438 t s x f).
Proof. exact (MK_COMB (@lem3451808 _89438) (@lem3451807 _89422 _89438 t s x f)). Qed.
Lemma lem3451810 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : ((term224 _89422 _89438 t s x f) = (term225 _89422 _89438 t s x f)) = ((term218 _89422 _89438 t s x f) = (term241 _89422 _89438 t s x f)).
Proof. exact (MK_COMB (@lem3451801 _89422 _89438 t s x f) (@lem3451809 _89422 _89438 t s x f)). Qed.
Lemma lem3451811 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term218 _89422 _89438 t s x f) = (term241 _89422 _89438 t s x f).
Proof. exact (EQ_MP (@lem3451810 _89422 _89438 t s x f) (@lem3451788 _89422 _89438 t s x f)). Qed.
Lemma lem3451812 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term220 _89422 _89438 s x f) = (term242 _89422 _89438 s x f).
Proof. exact (fun_ext (fun t : _89422 -> Prop => @lem3451811 _89422 _89438 t s x f)). Qed.
Lemma lem3451813 {_89422 : Type'} : (@ex (_89422 -> Prop)) = (@ex (_89422 -> Prop)).
Proof. exact (eq_refl (@ex (_89422 -> Prop))). Qed.
Lemma lem3451814 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term221 _89422 _89438 s x f) = (term243 _89422 _89438 s x f).
Proof. exact (MK_COMB (@lem3451813 _89422) (@lem3451812 _89422 _89438 s x f)). Qed.
Lemma lem3451815 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term202 _89422 _89438 s x f) = (term243 _89422 _89438 s x f).
Proof. exact (TRANS (@lem3451784 _89422 _89438 s x f) (@lem3451814 _89422 _89438 s x f)). Qed.
Lemma lem3451817 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term133 _89422 _89438 s x f) = (term243 _89422 _89438 s x f).
Proof. exact (TRANS (@lem3451758 _89422 _89438 s x f) (@lem3451815 _89422 _89438 s x f)). Qed.
Lemma lem3451818 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term86 _89422 _89438 s x f) = (term243 _89422 _89438 s x f).
Proof. exact (TRANS (@lem3451362 _89422 _89438 s x f) (@lem3451817 _89422 _89438 s x f)). Qed.
Lemma lem3451819 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term86 _89422 _89438 s x f) : term243 _89422 _89438 s x f.
Proof. exact (EQ_MP (@lem3451818 _89422 _89438 s x f) (@lem3451278 _89422 _89438 s x f h1)). Qed.
Lemma lem3451820 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term241 _89422 _89438 t s x f) : term241 _89422 _89438 t s x f.
Proof. exact (h1). Qed.
Lemma lem3451821 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) (h1 : term238 _89422 _89438 t s x f x') : term238 _89422 _89438 t s x f x'.
Proof. exact (h1). Qed.
Lemma lem3451836 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) : (term81 _89422 _89438 s x f x') = (term81 _89422 _89438 s x f x').
Proof. exact (eq_refl (term81 _89422 _89438 s x f x')). Qed.
Lemma lem3451843 {_89422 : Type'} (x : _89422) (t : _89422 -> Prop) : (term98 _89422 x t) = (term98 _89422 x t).
Proof. exact (eq_refl (term98 _89422 x t)). Qed.
Lemma lem3451862 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (x : _89438) (s : _89438 -> Prop) : (term88 _89422 _89438 t f x s) = (term88 _89422 _89438 t f x s).
Proof. exact (eq_refl (term88 _89422 _89438 t f x s)). Qed.
Lemma lem3451863 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (s : _89438 -> Prop) : (term96 _89422 _89438 t f s) = (term96 _89422 _89438 t f s).
Proof. exact (fun_ext (fun x : _89438 => @lem3451862 _89422 _89438 t f x s)). Qed.
Lemma lem3451864 {_89438 : Type'} : (@all _89438) = (@all _89438).
Proof. exact (eq_refl (@all _89438)). Qed.
Lemma lem3451865 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (s : _89438 -> Prop) : (term97 _89422 _89438 t f s) = (term97 _89422 _89438 t f s).
Proof. exact (MK_COMB (@lem3451864 _89438) (@lem3451863 _89422 _89438 t f s)). Qed.
Lemma lem3451866 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3451867 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (s : _89438 -> Prop) : (term100 _89422 _89438 t f s) = (term100 _89422 _89438 t f s).
Proof. exact (MK_COMB (@lem3451866) (@lem3451865 _89422 _89438 t f s)). Qed.
Lemma lem3451868 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term102 _89422 _89438 f s x t) = (term102 _89422 _89438 f s x t).
Proof. exact (MK_COMB (@lem3451867 _89422 _89438 t f s) (@lem3451843 _89422 x t)). Qed.
Lemma lem3451869 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term111 _89422 _89438 f s x) = (term111 _89422 _89438 f s x).
Proof. exact (fun_ext (fun t : _89422 -> Prop => @lem3451868 _89422 _89438 f s x t)). Qed.
Lemma lem3451870 {_89422 : Type'} : (@all (_89422 -> Prop)) = (@all (_89422 -> Prop)).
Proof. exact (eq_refl (@all (_89422 -> Prop))). Qed.
Lemma lem3451871 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term112 _89422 _89438 f s x) = (term112 _89422 _89438 f s x).
Proof. exact (MK_COMB (@lem3451870 _89422) (@lem3451869 _89422 _89438 f s x)). Qed.
Lemma lem3451872 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3451873 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term124 _89422 _89438 f s x) = (term124 _89422 _89438 f s x).
Proof. exact (MK_COMB (@lem3451872) (@lem3451871 _89422 _89438 f s x)). Qed.
Lemma lem3451874 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) : (term198 _89422 _89438 s x f x') = (term198 _89422 _89438 s x f x').
Proof. exact (MK_COMB (@lem3451873 _89422 _89438 f s x) (@lem3451836 _89422 _89438 s x f x')). Qed.
Lemma lem3451893 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) : (term114 _89422 _89438 s x f x') = (term114 _89422 _89438 s x f x').
Proof. exact (eq_refl (term114 _89422 _89438 s x f x')). Qed.
Lemma lem3451894 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term121 _89422 _89438 s x f) = (term121 _89422 _89438 s x f).
Proof. exact (fun_ext (fun x' : _89438 => @lem3451893 _89422 _89438 s x f x')). Qed.
Lemma lem3451895 {_89438 : Type'} : (@all _89438) = (@all _89438).
Proof. exact (eq_refl (@all _89438)). Qed.
Lemma lem3451896 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term122 _89422 _89438 s x f) = (term122 _89422 _89438 s x f).
Proof. exact (MK_COMB (@lem3451895 _89438) (@lem3451894 _89422 _89438 s x f)). Qed.
Lemma lem3451921 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (x' : _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term180 _89422 _89438 f x' s x t) = (term180 _89422 _89438 f x' s x t).
Proof. exact (eq_refl (term180 _89422 _89438 f x' s x t)). Qed.
Lemma lem3451922 {_89422 _89438 : Type'} (x' : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term182 _89422 _89438 x' t s x f) = (term182 _89422 _89438 x' t s x f).
Proof. exact (MK_COMB (@lem3451921 _89422 _89438 f x' s x t) (@lem3451896 _89422 _89438 s x f)). Qed.
Lemma lem3451923 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3451924 {_89422 _89438 : Type'} (x' : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term236 _89422 _89438 x' t s x f) = (term236 _89422 _89438 x' t s x f).
Proof. exact (MK_COMB (@lem3451923) (@lem3451922 _89422 _89438 x' t s x f)). Qed.
Lemma lem3451925 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) : (term238 _89422 _89438 t s x f x') = (term238 _89422 _89438 t s x f x').
Proof. exact (MK_COMB (@lem3451924 _89422 _89438 x' t s x f) (@lem3451874 _89422 _89438 s x f x')). Qed.
Lemma lem3451926 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) (h1 : term238 _89422 _89438 t s x f x') : term238 _89422 _89438 t s x f x'.
Proof. exact (EQ_MP (@lem3451925 _89422 _89438 t s x f x') (@lem3451821 _89422 _89438 t s x f x' h1)). Qed.
Lemma lem3451927 {_89422 _89438 : Type'} (x' : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term182 _89422 _89438 x' t s x f) : term182 _89422 _89438 x' t s x f.
Proof. exact (h1). Qed.
Lemma lem3451928 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) (h1 : term198 _89422 _89438 s x f x') : term198 _89422 _89438 s x f x'.
Proof. exact (h1). Qed.
Lemma lem3451929 {_89422 _89438 : Type'} (x' : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term182 _89422 _89438 x' t s x f) : term122 _89422 _89438 s x f.
Proof. exact (proj2 (@lem3451927 _89422 _89438 x' t s x f h1)). Qed.
Lemma lem3451930 {_89422 _89438 : Type'} (x' : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term182 _89422 _89438 x' t s x f) : term146 _89422 _89438 f x' s x t.
Proof. exact (proj1 (@lem3451927 _89422 _89438 x' t s x f h1)). Qed.
Lemma lem3451932 {_89422 _89438 : Type'} (x' : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term182 _89422 _89438 x' t s x f) : term83 _89422 _89438 t f x' s.
Proof. exact (proj1 (@lem3451930 _89422 _89438 x' t s x f h1)). Qed.
Lemma lem3451935 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) (h1 : term198 _89422 _89438 s x f x') : term81 _89422 _89438 s x f x'.
Proof. exact (proj2 (@lem3451928 _89422 _89438 s x f x' h1)). Qed.
Lemma lem3451936 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) (h1 : term198 _89422 _89438 s x f x') : term112 _89422 _89438 f s x.
Proof. exact (proj1 (@lem3451928 _89422 _89438 s x f x' h1)). Qed.
Lemma lem3451946 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) : (term114 _89422 _89438 s x f x') = (term114 _89422 _89438 s x f x').
Proof. exact (eq_refl (term114 _89422 _89438 s x f x')). Qed.
Lemma lem3451947 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term121 _89422 _89438 s x f) = (term121 _89422 _89438 s x f).
Proof. exact (fun_ext (fun x' : _89438 => @lem3451946 _89422 _89438 s x f x')). Qed.
Lemma lem3451948 {_89438 : Type'} : (@all _89438) = (@all _89438).
Proof. exact (eq_refl (@all _89438)). Qed.
Lemma lem3451950 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term122 _89422 _89438 s x f) = (term122 _89422 _89438 s x f).
Proof. exact (MK_COMB (@lem3451948 _89438) (@lem3451947 _89422 _89438 s x f)). Qed.
Lemma lem3451951 {_89422 _89438 : Type'} (x' : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term182 _89422 _89438 x' t s x f) : term122 _89422 _89438 s x f.
Proof. exact (EQ_MP (@lem3451950 _89422 _89438 s x f) (@lem3451929 _89422 _89438 x' t s x f h1)). Qed.
Lemma lem3451965 {A : Type'} (P : A -> Prop) (Q : Prop) : (term244 A P Q) = (term245 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3451966 {_89438 : Type'} (P : _89438 -> Prop) (Q : Prop) : (term244 _89438 P Q) = (term245 _89438 P Q).
Proof. exact (@lem3451965 _89438 P Q). Qed.
Lemma lem3451967 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term246 _89422 _89438 f s x t) = (term247 _89422 _89438 f s x t).
Proof. exact (@lem3451966 _89438 (term96 _89422 _89438 t f s) (term98 _89422 x t)). Qed.
Lemma lem3451968 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (x : _89438) (s : _89438 -> Prop) : (term248 _89422 _89438 t f s x) = (term88 _89422 _89438 t f x s).
Proof. exact (eq_refl (term248 _89422 _89438 t f s x)). Qed.
Lemma lem3451969 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (s : _89438 -> Prop) : (term249 _89422 _89438 t f s) = (term96 _89422 _89438 t f s).
Proof. exact (fun_ext (fun x : _89438 => @lem3451968 _89422 _89438 t f x s)). Qed.
Lemma lem3451970 {_89438 : Type'} : (@all _89438) = (@all _89438).
Proof. exact (eq_refl (@all _89438)). Qed.
Lemma lem3451971 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (s : _89438 -> Prop) : (term250 _89422 _89438 t f s) = (term97 _89422 _89438 t f s).
Proof. exact (MK_COMB (@lem3451970 _89438) (@lem3451969 _89422 _89438 t f s)). Qed.
Lemma lem3451972 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3451973 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (s : _89438 -> Prop) : (term251 _89422 _89438 t f s) = (term100 _89422 _89438 t f s).
Proof. exact (MK_COMB (@lem3451972) (@lem3451971 _89422 _89438 t f s)). Qed.
Lemma lem3451974 {_89422 : Type'} (x : _89422) (t : _89422 -> Prop) : (term98 _89422 x t) = (term98 _89422 x t).
Proof. exact (eq_refl (term98 _89422 x t)). Qed.
Lemma lem3451975 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term246 _89422 _89438 f s x t) = (term102 _89422 _89438 f s x t).
Proof. exact (MK_COMB (@lem3451973 _89422 _89438 t f s) (@lem3451974 _89422 x t)). Qed.
Lemma lem3451976 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3451977 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term252 _89422 _89438 f s x t) = (term253 _89422 _89438 f s x t).
Proof. exact (MK_COMB (@lem3451976) (@lem3451975 _89422 _89438 f s x t)). Qed.
Lemma lem3451978 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (x : _89438) (s : _89438 -> Prop) : (term248 _89422 _89438 t f s x) = (term88 _89422 _89438 t f x s).
Proof. exact (eq_refl (term248 _89422 _89438 t f s x)). Qed.
Lemma lem3451979 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3451980 {_89422 _89438 : Type'} (t : _89422 -> Prop) (f : type1470 _89422 _89438) (x : _89438) (s : _89438 -> Prop) : (term254 _89422 _89438 t f s x) = (term255 _89422 _89438 t f x s).
Proof. exact (MK_COMB (@lem3451979) (@lem3451978 _89422 _89438 t f x s)). Qed.
Lemma lem3451981 {_89422 : Type'} (x : _89422) (t : _89422 -> Prop) : (term98 _89422 x t) = (term98 _89422 x t).
Proof. exact (eq_refl (term98 _89422 x t)). Qed.
Lemma lem3451982 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (x : _89438) (s : _89438 -> Prop) (x' : _89422) (t : _89422 -> Prop) : (term256 _89422 _89438 f s x x' t) = (term257 _89422 _89438 f x s x' t).
Proof. exact (MK_COMB (@lem3451980 _89422 _89438 t f x s) (@lem3451981 _89422 x' t)). Qed.
Lemma lem3451983 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term258 _89422 _89438 f s x t) = (term259 _89422 _89438 f s x t).
Proof. exact (fun_ext (fun x' : _89438 => @lem3451982 _89422 _89438 f x' s x t)). Qed.
Lemma lem3451984 {_89438 : Type'} : (@all _89438) = (@all _89438).
Proof. exact (eq_refl (@all _89438)). Qed.
Lemma lem3451985 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term247 _89422 _89438 f s x t) = (term260 _89422 _89438 f s x t).
Proof. exact (MK_COMB (@lem3451984 _89438) (@lem3451983 _89422 _89438 f s x t)). Qed.
Lemma lem3451986 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : ((term246 _89422 _89438 f s x t) = (term247 _89422 _89438 f s x t)) = ((term102 _89422 _89438 f s x t) = (term260 _89422 _89438 f s x t)).
Proof. exact (MK_COMB (@lem3451977 _89422 _89438 f s x t) (@lem3451985 _89422 _89438 f s x t)). Qed.
Lemma lem3451987 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term102 _89422 _89438 f s x t) = (term260 _89422 _89438 f s x t).
Proof. exact (EQ_MP (@lem3451986 _89422 _89438 f s x t) (@lem3451967 _89422 _89438 f s x t)). Qed.
Lemma lem3451988 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term111 _89422 _89438 f s x) = (term261 _89422 _89438 f s x).
Proof. exact (fun_ext (fun t : _89422 -> Prop => @lem3451987 _89422 _89438 f s x t)). Qed.
Lemma lem3451989 {_89422 : Type'} : (@all (_89422 -> Prop)) = (@all (_89422 -> Prop)).
Proof. exact (eq_refl (@all (_89422 -> Prop))). Qed.
Lemma lem3451990 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term112 _89422 _89438 f s x) = (term262 _89422 _89438 f s x).
Proof. exact (MK_COMB (@lem3451989 _89422) (@lem3451988 _89422 _89438 f s x)). Qed.
Lemma lem3452003 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (x : _89438) (s : _89438 -> Prop) (x' : _89422) (t : _89422 -> Prop) : (term257 _89422 _89438 f x s x' t) = (term257 _89422 _89438 f x s x' t).
Proof. exact (eq_refl (term257 _89422 _89438 f x s x' t)). Qed.
Lemma lem3452004 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term259 _89422 _89438 f s x t) = (term259 _89422 _89438 f s x t).
Proof. exact (fun_ext (fun x' : _89438 => @lem3452003 _89422 _89438 f x' s x t)). Qed.
Lemma lem3452005 {_89438 : Type'} : (@all _89438) = (@all _89438).
Proof. exact (eq_refl (@all _89438)). Qed.
Lemma lem3452006 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (t : _89422 -> Prop) : (term260 _89422 _89438 f s x t) = (term260 _89422 _89438 f s x t).
Proof. exact (MK_COMB (@lem3452005 _89438) (@lem3452004 _89422 _89438 f s x t)). Qed.
Lemma lem3452007 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term261 _89422 _89438 f s x) = (term261 _89422 _89438 f s x).
Proof. exact (fun_ext (fun t : _89422 -> Prop => @lem3452006 _89422 _89438 f s x t)). Qed.
Lemma lem3452008 {_89422 : Type'} : (@all (_89422 -> Prop)) = (@all (_89422 -> Prop)).
Proof. exact (eq_refl (@all (_89422 -> Prop))). Qed.
Lemma lem3452009 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term262 _89422 _89438 f s x) = (term262 _89422 _89438 f s x).
Proof. exact (MK_COMB (@lem3452008 _89422) (@lem3452007 _89422 _89438 f s x)). Qed.
Lemma lem3452010 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) : (term112 _89422 _89438 f s x) = (term262 _89422 _89438 f s x).
Proof. exact (TRANS (@lem3451990 _89422 _89438 f s x) (@lem3452009 _89422 _89438 f s x)). Qed.
Lemma lem3452011 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) (h1 : term198 _89422 _89438 s x f x') : term262 _89422 _89438 f s x.
Proof. exact (EQ_MP (@lem3452010 _89422 _89438 f s x) (@lem3451936 _89422 _89438 s x f x' h1)). Qed.
Lemma lem3452020 {_89422 _89438 : Type'} (_36391 : _89438) (x' : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term182 _89422 _89438 x' t s x f) : term263 _89422 _89438 s x f _36391.
Proof. exact (@lem3451951 _89422 _89438 x' t s x f h1 _36391). Qed.
Lemma lem3452021 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (_36391 : _89438) : (term263 _89422 _89438 s x f _36391) = (term114 _89422 _89438 s x f _36391).
Proof. exact (eq_refl (term263 _89422 _89438 s x f _36391)). Qed.
Lemma lem3452023 {_89422 _89438 : Type'} (_36392 : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) (h1 : term198 _89422 _89438 s x f x') : term264 _89422 _89438 f s x _36392.
Proof. exact (@lem3452011 _89422 _89438 s x f x' h1 _36392). Qed.
Lemma lem3452024 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) (x : _89422) (_36392 : _89422 -> Prop) : (term264 _89422 _89438 f s x _36392) = (term260 _89422 _89438 f s x _36392).
Proof. exact (eq_refl (term264 _89422 _89438 f s x _36392)). Qed.
Lemma lem3452025 {_89422 _89438 : Type'} (_36392 : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) (h1 : term198 _89422 _89438 s x f x') : term260 _89422 _89438 f s x _36392.
Proof. exact (EQ_MP (@lem3452024 _89422 _89438 f s x _36392) (@lem3452023 _89422 _89438 _36392 s x f x' h1)). Qed.
Lemma lem3452026 {_89422 _89438 : Type'} (_36392 : _89422 -> Prop) (_36393 : _89438) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) (h1 : term198 _89422 _89438 s x f x') : term265 _89422 _89438 f s x _36392 _36393.
Proof. exact (@lem3452025 _89422 _89438 _36392 s x f x' h1 _36393). Qed.
Lemma lem3452027 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (_36393 : _89438) (s : _89438 -> Prop) (x : _89422) (_36392 : _89422 -> Prop) : (term265 _89422 _89438 f s x _36392 _36393) = (term257 _89422 _89438 f _36393 s x _36392).
Proof. exact (eq_refl (term265 _89422 _89438 f s x _36392 _36393)). Qed.
Lemma lem3452028 {_89422 _89438 : Type'} (_36393 : _89438) (_36392 : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) (h1 : term198 _89422 _89438 s x f x') : term257 _89422 _89438 f _36393 s x _36392.
Proof. exact (EQ_MP (@lem3452027 _89422 _89438 f _36393 s x _36392) (@lem3452026 _89422 _89438 _36392 _36393 s x f x' h1)). Qed.
Lemma lem3452036 {_89422 _89438 : Type'} (x' : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term182 _89422 _89438 x' t s x f) : @IN _89422 x t.
Proof. exact (proj2 (@lem3451930 _89422 _89438 x' t s x f h1)). Qed.
Lemma lem3452038 {_89422 _89438 : Type'} (x' : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term182 _89422 _89438 x' t s x f) : t = (f x').
Proof. exact (proj1 (@lem3451932 _89422 _89438 x' t s x f h1)). Qed.
Lemma lem3452051 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (_36393 : _89438) (s : _89438 -> Prop) (x : _89422) (_36392 : _89422 -> Prop) : (term257 _89422 _89438 f _36393 s x _36392) = (term266 _89422 _89438 f _36393 s x _36392).
Proof. exact (@lem3450837 (term267 _89422 _89438 _36392 f _36393) (term98 _89438 _36393 s) (term98 _89422 x _36392)). Qed.
Lemma lem3452052 {_89422 _89438 : Type'} (_36393 : _89438) (_36392 : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) (h1 : term198 _89422 _89438 s x f x') : term266 _89422 _89438 f _36393 s x _36392.
Proof. exact (EQ_MP (@lem3452051 _89422 _89438 f _36393 s x _36392) (@lem3452028 _89422 _89438 _36393 _36392 s x f x' h1)). Qed.
Lemma lem3452084 {_89422 _89438 : Type'} (_36391 : _89438) (x' : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term182 _89422 _89438 x' t s x f) : term114 _89422 _89438 s x f _36391.
Proof. exact (EQ_MP (@lem3452021 _89422 _89438 s x f _36391) (@lem3452020 _89422 _89438 _36391 x' t s x f h1)). Qed.
Lemma lem3452085 {_89422 : Type'} (x : _89422) : (term268 _89422 x) = (term268 _89422 x).
Proof. exact (eq_refl (term268 _89422 x)). Qed.
Lemma lem3452086 {_89422 _89438 : Type'} (x' : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term182 _89422 _89438 x' t s x f) : (term269 _89422 x t) = (term270 _89422 _89438 x f x').
Proof. exact (MK_COMB (@lem3452085 _89422 x) (@lem3452038 _89422 _89438 x' t s x f h1)). Qed.
Lemma lem3452087 {_89422 _89438 : Type'} (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) : (term270 _89422 _89438 x f x') = (term115 _89422 _89438 x f x').
Proof. exact (eq_refl (term270 _89422 _89438 x f x')). Qed.
Lemma lem3452088 {_89422 : Type'} (x : _89422) (t : _89422 -> Prop) : (term271 _89422 x t) = (term271 _89422 x t).
Proof. exact (eq_refl (term271 _89422 x t)). Qed.
Lemma lem3452089 {_89422 _89438 : Type'} (t : _89422 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) : ((term269 _89422 x t) = (term270 _89422 _89438 x f x')) = ((term269 _89422 x t) = (term115 _89422 _89438 x f x')).
Proof. exact (MK_COMB (@lem3452088 _89422 x t) (@lem3452087 _89422 _89438 x f x')). Qed.
Lemma lem3452090 {_89422 : Type'} (x : _89422) (t : _89422 -> Prop) : (term269 _89422 x t) = (@IN _89422 x t).
Proof. exact (eq_refl (term269 _89422 x t)). Qed.
Lemma lem3452091 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3452092 {_89422 : Type'} (x : _89422) (t : _89422 -> Prop) : (term271 _89422 x t) = (term272 _89422 x t).
Proof. exact (MK_COMB (@lem3452091) (@lem3452090 _89422 x t)). Qed.
Lemma lem3452093 {_89422 _89438 : Type'} (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) : (term115 _89422 _89438 x f x') = (term115 _89422 _89438 x f x').
Proof. exact (eq_refl (term115 _89422 _89438 x f x')). Qed.
Lemma lem3452094 {_89422 _89438 : Type'} (t : _89422 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) : ((term269 _89422 x t) = (term115 _89422 _89438 x f x')) = ((@IN _89422 x t) = (term115 _89422 _89438 x f x')).
Proof. exact (MK_COMB (@lem3452092 _89422 x t) (@lem3452093 _89422 _89438 x f x')). Qed.
Lemma lem3452095 {_89422 _89438 : Type'} (t : _89422 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) : ((term269 _89422 x t) = (term270 _89422 _89438 x f x')) = ((@IN _89422 x t) = (term115 _89422 _89438 x f x')).
Proof. exact (TRANS (@lem3452089 _89422 _89438 t x f x') (@lem3452094 _89422 _89438 t x f x')). Qed.
Lemma lem3452096 {_89422 _89438 : Type'} (x' : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term182 _89422 _89438 x' t s x f) : (@IN _89422 x t) = (term115 _89422 _89438 x f x').
Proof. exact (EQ_MP (@lem3452095 _89422 _89438 t x f x') (@lem3452086 _89422 _89438 x' t s x f h1)). Qed.
Lemma lem3452113 {_89422 _89438 : Type'} (x' : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term182 _89422 _89438 x' t s x f) : @IN _89438 x' s.
Proof. exact (proj2 (@lem3451932 _89422 _89438 x' t s x f h1)). Qed.
Lemma lem3452114 {_89422 _89438 : Type'} (x' : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term182 _89422 _89438 x' t s x f) : term273 _89438 x' s.
Proof. exact (fun h0 : term98 _89438 x' s => @lem3452113 _89422 _89438 x' t s x f h1). Qed.
Lemma lem3452116 (p : Prop) : (term274 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3452117 {_89438 : Type'} (x' : _89438) (s : _89438 -> Prop) : (term273 _89438 x' s) = (@IN _89438 x' s).
Proof. exact (@lem3452116 (@IN _89438 x' s)). Qed.
Lemma lem3452118 {_89422 _89438 : Type'} (x' : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term182 _89422 _89438 x' t s x f) : @IN _89438 x' s.
Proof. exact (EQ_MP (@lem3452117 _89438 x' s) (@lem3452114 _89422 _89438 x' t s x f h1)). Qed.
Lemma lem3452120 {_89422 _89438 : Type'} (x' : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term182 _89422 _89438 x' t s x f) : term115 _89422 _89438 x f x'.
Proof. exact (EQ_MP (@lem3452096 _89422 _89438 x' t s x f h1) (@lem3452036 _89422 _89438 x' t s x f h1)). Qed.
Lemma lem3452121 {_89422 _89438 : Type'} (x' : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term182 _89422 _89438 x' t s x f) : term275 _89422 _89438 x f x'.
Proof. exact (fun h0 : term276 _89422 _89438 x f x' => @lem3452120 _89422 _89438 x' t s x f h1). Qed.
Lemma lem3452123 (p : Prop) : (term274 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3452124 {_89422 _89438 : Type'} (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) : (term275 _89422 _89438 x f x') = (term115 _89422 _89438 x f x').
Proof. exact (@lem3452123 (term115 _89422 _89438 x f x')). Qed.
Lemma lem3452125 {_89422 _89438 : Type'} (x' : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term182 _89422 _89438 x' t s x f) : term115 _89422 _89438 x f x'.
Proof. exact (EQ_MP (@lem3452124 _89422 _89438 x f x') (@lem3452121 _89422 _89438 x' t s x f h1)). Qed.
Lemma lem3452127 (a : Prop) (b : Prop) : (term277 a b) = (term278 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3452128 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (_36391 : _89438) : (term114 _89422 _89438 s x f _36391) = (term113 _89422 _89438 s x f _36391).
Proof. exact (@lem3452127 (@IN _89438 _36391 s) (term115 _89422 _89438 x f _36391)). Qed.
Lemma lem3452130 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3452131 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (_36391 : _89438) : (term113 _89422 _89438 s x f _36391) = (term279 _89422 _89438 s x f _36391).
Proof. exact (@lem3452130 (term81 _89422 _89438 s x f _36391)). Qed.
Lemma lem3452132 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (_36391 : _89438) : (term114 _89422 _89438 s x f _36391) = (term279 _89422 _89438 s x f _36391).
Proof. exact (TRANS (@lem3452128 _89422 _89438 s x f _36391) (@lem3452131 _89422 _89438 s x f _36391)). Qed.
Lemma lem3452134 {_89422 _89438 : Type'} (x' : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term182 _89422 _89438 x' t s x f) : term81 _89422 _89438 s x f x'.
Proof. exact (conj (@lem3452118 _89422 _89438 x' t s x f h1) (@lem3452125 _89422 _89438 x' t s x f h1)). Qed.
Lemma lem3452136 {_89422 _89438 : Type'} (_36391 : _89438) (x' : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term182 _89422 _89438 x' t s x f) : term279 _89422 _89438 s x f _36391.
Proof. exact (EQ_MP (@lem3452132 _89422 _89438 s x f _36391) (@lem3452084 _89422 _89438 _36391 x' t s x f h1)). Qed.
Lemma lem3452137 {_89422 _89438 : Type'} (_36391 : _89438) (x' : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term182 _89422 _89438 x' t s x f) : term279 _89422 _89438 s x f _36391.
Proof. exact (@lem3452136 _89422 _89438 _36391 x' t s x f h1). Qed.
Lemma lem3452138 {_89422 _89438 : Type'} (x' : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term182 _89422 _89438 x' t s x f) : term279 _89422 _89438 s x f x'.
Proof. exact (@lem3452137 _89422 _89438 x' x' t s x f h1). Qed.
Lemma lem3452141 {_89422 _89438 : Type'} (x' : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term182 _89422 _89438 x' t s x f) : False.
Proof. exact (@lem3452138 _89422 _89438 x' t s x f h1 (@lem3452134 _89422 _89438 x' t s x f h1)). Qed.
Lemma lem3452142 {_89422 _89438 : Type'} (x' : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term182 _89422 _89438 x' t s x f) : term280.
Proof. exact (fun h0 : ~ False => @lem3452141 _89422 _89438 x' t s x f h1). Qed.
Lemma lem3452144 (p : Prop) : (term274 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3452145 : term280 = False.
Proof. exact (@lem3452144 False). Qed.
Lemma lem3452202 {_89422 : Type'} (x : _89422 -> Prop) : x = x.
Proof. exact (@lem21386 (_89422 -> Prop) x). Qed.
Lemma lem3452203 {_89422 : Type'} (x : _89422 -> Prop) : x = x.
Proof. exact (@lem3452202 _89422 x). Qed.
Lemma lem3452204 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (x' : _89438) : (f x') = (f x').
Proof. exact (@lem3452203 _89422 (f x')). Qed.
Lemma lem3452205 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (x' : _89438) : term281 _89422 _89438 f x'.
Proof. exact (fun h0 : term282 _89422 _89438 f x' => @lem3452204 _89422 _89438 f x'). Qed.
Lemma lem3452207 (p : Prop) : (term274 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3452208 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (x' : _89438) : (term281 _89422 _89438 f x') = ((f x') = (f x')).
Proof. exact (@lem3452207 ((f x') = (f x'))). Qed.
Lemma lem3452209 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (x' : _89438) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3452208 _89422 _89438 f x') (@lem3452205 _89422 _89438 f x')). Qed.
Lemma lem3452211 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) (h1 : term198 _89422 _89438 s x f x') : @IN _89438 x' s.
Proof. exact (proj1 (@lem3451935 _89422 _89438 s x f x' h1)). Qed.
Lemma lem3452212 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) (h1 : term198 _89422 _89438 s x f x') : term273 _89438 x' s.
Proof. exact (fun h0 : term98 _89438 x' s => @lem3452211 _89422 _89438 s x f x' h1). Qed.
Lemma lem3452214 (p : Prop) : (term274 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3452215 {_89438 : Type'} (x' : _89438) (s : _89438 -> Prop) : (term273 _89438 x' s) = (@IN _89438 x' s).
Proof. exact (@lem3452214 (@IN _89438 x' s)). Qed.
Lemma lem3452216 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) (h1 : term198 _89422 _89438 s x f x') : @IN _89438 x' s.
Proof. exact (EQ_MP (@lem3452215 _89438 x' s) (@lem3452212 _89422 _89438 s x f x' h1)). Qed.
Lemma lem3452218 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) (h1 : term198 _89422 _89438 s x f x') : term115 _89422 _89438 x f x'.
Proof. exact (proj2 (@lem3451935 _89422 _89438 s x f x' h1)). Qed.
Lemma lem3452219 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) (h1 : term198 _89422 _89438 s x f x') : term275 _89422 _89438 x f x'.
Proof. exact (fun h0 : term276 _89422 _89438 x f x' => @lem3452218 _89422 _89438 s x f x' h1). Qed.
Lemma lem3452221 (p : Prop) : (term274 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3452222 {_89422 _89438 : Type'} (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) : (term275 _89422 _89438 x f x') = (term115 _89422 _89438 x f x').
Proof. exact (@lem3452221 (term115 _89422 _89438 x f x')). Qed.
Lemma lem3452223 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) (h1 : term198 _89422 _89438 s x f x') : term115 _89422 _89438 x f x'.
Proof. exact (EQ_MP (@lem3452222 _89422 _89438 x f x') (@lem3452219 _89422 _89438 s x f x' h1)). Qed.
Lemma lem3452225 (a : Prop) (b : Prop) : (term277 a b) = (term278 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3452226 {_89422 _89438 : Type'} (_36393 : _89438) (s : _89438 -> Prop) (x : _89422) (_36392 : _89422 -> Prop) : (term283 _89422 _89438 _36393 s x _36392) = (term284 _89422 _89438 _36393 s x _36392).
Proof. exact (@lem3452225 (@IN _89438 _36393 s) (@IN _89422 x _36392)). Qed.
Lemma lem3452227 {_89422 _89438 : Type'} (_36392 : _89422 -> Prop) (f : type1470 _89422 _89438) (_36393 : _89438) : (term285 _89422 _89438 _36392 f _36393) = (term285 _89422 _89438 _36392 f _36393).
Proof. exact (eq_refl (term285 _89422 _89438 _36392 f _36393)). Qed.
Lemma lem3452228 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (_36393 : _89438) (s : _89438 -> Prop) (x : _89422) (_36392 : _89422 -> Prop) : (term266 _89422 _89438 f _36393 s x _36392) = (term286 _89422 _89438 f _36393 s x _36392).
Proof. exact (MK_COMB (@lem3452227 _89422 _89438 _36392 f _36393) (@lem3452226 _89422 _89438 _36393 s x _36392)). Qed.
Lemma lem3452230 (a : Prop) (b : Prop) : (term277 a b) = (term278 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3452231 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (_36393 : _89438) (s : _89438 -> Prop) (x : _89422) (_36392 : _89422 -> Prop) : (term286 _89422 _89438 f _36393 s x _36392) = (term287 _89422 _89438 f _36393 s x _36392).
Proof. exact (@lem3452230 (_36392 = (f _36393)) (term288 _89422 _89438 _36393 s x _36392)). Qed.
Lemma lem3452232 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (_36393 : _89438) (s : _89438 -> Prop) (x : _89422) (_36392 : _89422 -> Prop) : (term266 _89422 _89438 f _36393 s x _36392) = (term287 _89422 _89438 f _36393 s x _36392).
Proof. exact (TRANS (@lem3452228 _89422 _89438 f _36393 s x _36392) (@lem3452231 _89422 _89438 f _36393 s x _36392)). Qed.
Lemma lem3452234 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3452235 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (_36393 : _89438) (s : _89438 -> Prop) (x : _89422) (_36392 : _89422 -> Prop) : (term287 _89422 _89438 f _36393 s x _36392) = (term289 _89422 _89438 f _36393 s x _36392).
Proof. exact (@lem3452234 (term290 _89422 _89438 f _36393 s x _36392)). Qed.
Lemma lem3452236 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (_36393 : _89438) (s : _89438 -> Prop) (x : _89422) (_36392 : _89422 -> Prop) : (term266 _89422 _89438 f _36393 s x _36392) = (term289 _89422 _89438 f _36393 s x _36392).
Proof. exact (TRANS (@lem3452232 _89422 _89438 f _36393 s x _36392) (@lem3452235 _89422 _89438 f _36393 s x _36392)). Qed.
Lemma lem3452238 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) (h1 : term198 _89422 _89438 s x f x') : term81 _89422 _89438 s x f x'.
Proof. exact (conj (@lem3452216 _89422 _89438 s x f x' h1) (@lem3452223 _89422 _89438 s x f x' h1)). Qed.
Lemma lem3452239 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) (h1 : term198 _89422 _89438 s x f x') : term291 _89422 _89438 s x f x'.
Proof. exact (conj (@lem3452209 _89422 _89438 f x') (@lem3452238 _89422 _89438 s x f x' h1)). Qed.
Lemma lem3452241 {_89422 _89438 : Type'} (_36393 : _89438) (_36392 : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) (h1 : term198 _89422 _89438 s x f x') : term289 _89422 _89438 f _36393 s x _36392.
Proof. exact (EQ_MP (@lem3452236 _89422 _89438 f _36393 s x _36392) (@lem3452052 _89422 _89438 _36393 _36392 s x f x' h1)). Qed.
Lemma lem3452242 {_89422 _89438 : Type'} (_36393 : _89438) (_36392 : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) (h1 : term198 _89422 _89438 s x f x') : term289 _89422 _89438 f _36393 s x _36392.
Proof. exact (@lem3452241 _89422 _89438 _36393 _36392 s x f x' h1). Qed.
Lemma lem3452243 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) (h1 : term198 _89422 _89438 s x f x') : term292 _89422 _89438 s x f x'.
Proof. exact (@lem3452242 _89422 _89438 x' (f x') s x f x' h1). Qed.
Lemma lem3452246 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) (h1 : term198 _89422 _89438 s x f x') : False.
Proof. exact (@lem3452243 _89422 _89438 s x f x' h1 (@lem3452239 _89422 _89438 s x f x' h1)). Qed.
Lemma lem3452247 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) (h1 : term198 _89422 _89438 s x f x') : term280.
Proof. exact (fun h0 : ~ False => @lem3452246 _89422 _89438 s x f x' h1). Qed.
Lemma lem3452249 (p : Prop) : (term274 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3452250 : term280 = False.
Proof. exact (@lem3452249 False). Qed.
Lemma lem3452251 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) (h1 : term198 _89422 _89438 s x f x') : False.
Proof. exact (EQ_MP (@lem3452250) (@lem3452247 _89422 _89438 s x f x' h1)). Qed.
Lemma lem3452252 {_89422 _89438 : Type'} (x' : _89438) (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term182 _89422 _89438 x' t s x f) : False.
Proof. exact (EQ_MP (@lem3452145) (@lem3452142 _89422 _89438 x' t s x f h1)). Qed.
Lemma lem3452253 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) (h1 : term238 _89422 _89438 t s x f x') : False.
Proof. exact (or_elim (@lem3451926 _89422 _89438 t s x f x' h1) (fun h0 : term182 _89422 _89438 x' t s x f => @lem3452252 _89422 _89438 x' t s x f h0) (fun h0 : term198 _89422 _89438 s x f x' => @lem3452251 _89422 _89438 s x f x' h0)). Qed.
Lemma lem3452254 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) (h1 : term238 _89422 _89438 t s x f x') : (term238 _89422 _89438 t s x f x') = False.
Proof. exact (prop_ext (fun h2 : term238 _89422 _89438 t s x f x' => @lem3452253 _89422 _89438 t s x f x' h1) (fun h2 : False => @lem3451926 _89422 _89438 t s x f x' h1)). Qed.
Lemma lem3452255 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (x' : _89438) (h1 : term238 _89422 _89438 t s x f x') : False.
Proof. exact (EQ_MP (@lem3452254 _89422 _89438 t s x f x' h1) (@lem3451926 _89422 _89438 t s x f x' h1)). Qed.
Lemma lem3452256 {_89422 _89438 : Type'} (t : _89422 -> Prop) (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term241 _89422 _89438 t s x f) : False.
Proof. exact (ex_elim (@lem3451820 _89422 _89438 t s x f h1) (fun x' : _89438 => fun h0 : term240 _89422 _89438 t s x f x' => @lem3452255 _89422 _89438 t s x f x' h0)). Qed.
Lemma lem3452257 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term86 _89422 _89438 s x f) : False.
Proof. exact (ex_elim (@lem3451819 _89422 _89438 s x f h1) (fun t : _89422 -> Prop => fun h0 : term242 _89422 _89438 s x f t => @lem3452256 _89422 _89438 t s x f h0)). Qed.
Lemma lem3452258 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term86 _89422 _89438 s x f) : (term86 _89422 _89438 s x f) = False.
Proof. exact (prop_ext (fun h2 : term86 _89422 _89438 s x f => @lem3452257 _89422 _89438 s x f h1) (fun h2 : False => @lem3451278 _89422 _89438 s x f h1)). Qed.
Lemma lem3452259 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) (h1 : term86 _89422 _89438 s x f) : False.
Proof. exact (EQ_MP (@lem3452258 _89422 _89438 s x f h1) (@lem3451278 _89422 _89438 s x f h1)). Qed.
Lemma lem3452260 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : term85 _89422 _89438 s x f.
Proof. exact (fun h0 : term86 _89422 _89438 s x f => @lem3452259 _89422 _89438 s x f h0). Qed.
Lemma lem3452261 {_89422 _89438 : Type'} (s : _89438 -> Prop) (x : _89422) (f : type1470 _89422 _89438) : (term41 _89422 _89438 f s x) = (term47 _89422 _89438 s x f).
Proof. exact (EQ_MP (@lem3451277 _89422 _89438 s x f) (@lem3452260 _89422 _89438 s x f)). Qed.
Lemma lem3452266 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : term64 _89422 _89438 s f.
Proof. exact (fun x : _89422 => @lem3452261 _89422 _89438 s x f). Qed.
Lemma lem3452271 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) : term76 _89422 _89438 f.
Proof. exact (fun s : _89438 -> Prop => @lem3452266 _89422 _89438 s f). Qed.
Lemma lem3452276 {_89422 _89438 : Type'} : term80 _89422 _89438.
Proof. exact (fun f : type1470 _89422 _89438 => @lem3452271 _89422 _89438 f). Qed.
Lemma lem3452277 {_89422 _89438 : Type'} : term79 _89422 _89438.
Proof. exact (EQ_MP (@lem3451273 _89422 _89438) (@lem3452276 _89422 _89438)). Qed.
Lemma lem3452278 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) : term293 _89422 _89438 f.
Proof. exact (@lem3452277 _89422 _89438 f). Qed.
Lemma lem3452279 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) : (term293 _89422 _89438 f) = (term75 _89422 _89438 f).
Proof. exact (eq_refl (term293 _89422 _89438 f)). Qed.
Lemma lem3452280 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) : term75 _89422 _89438 f.
Proof. exact (EQ_MP (@lem3452279 _89422 _89438 f) (@lem3452278 _89422 _89438 f)). Qed.
Lemma lem3452281 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) : term294 _89422 _89438 f s.
Proof. exact (@lem3452280 _89422 _89438 f s). Qed.
Lemma lem3452282 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term294 _89422 _89438 f s) = (term66 _89422 _89438 s f).
Proof. exact (eq_refl (term294 _89422 _89438 f s)). Qed.
Lemma lem3452283 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : term66 _89422 _89438 s f.
Proof. exact (EQ_MP (@lem3452282 _89422 _89438 s f) (@lem3452281 _89422 _89438 f s)). Qed.
Lemma lem3452285 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : term66 _89422 _89438 s f.
Proof. exact (@lem3451005 _89422 _89438 s f (@lem3452283 _89422 _89438 s f)). Qed.
Lemma lem3452286 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) (h1 : term67 _89422 _89438 s f) : False.
Proof. exact (@lem3452285 _89422 _89438 s f (@lem3450989 _89422 _89438 s f h1)). Qed.
Lemma lem3452287 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) (h1 : term67 _89422 _89438 s f) : (term67 _89422 _89438 s f) = False.
Proof. exact (prop_ext (fun h2 : term67 _89422 _89438 s f => @lem3452286 _89422 _89438 s f h1) (fun h2 : False => @lem3450989 _89422 _89438 s f h1)). Qed.
Lemma lem3452288 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) (h1 : term67 _89422 _89438 s f) : False.
Proof. exact (EQ_MP (@lem3452287 _89422 _89438 s f h1) (@lem3450989 _89422 _89438 s f h1)). Qed.
Lemma lem3452289 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : term66 _89422 _89438 s f.
Proof. exact (fun h0 : term67 _89422 _89438 s f => @lem3452288 _89422 _89438 s f h0). Qed.
Lemma lem3452290 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : term64 _89422 _89438 s f.
Proof. exact (EQ_MP (@lem3450988 _89422 _89438 s f) (@lem3452289 _89422 _89438 s f)). Qed.
Lemma lem3452291 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : term30 _89422 _89438 s f.
Proof. exact (EQ_MP (@lem3450984 _89422 _89438 s f) (@lem3452290 _89422 _89438 s f)). Qed.
Lemma lem3452292 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term28 _89422 _89438 f s) = (term29 _89422 _89438 s f).
Proof. exact (EQ_MP (@lem3450901 _89422 _89438 s f) (@lem3452291 _89422 _89438 s f)). Qed.
Lemma lem3452297 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) : term295 _89422 _89438 f.
Proof. exact (fun s : _89438 -> Prop => @lem3452292 _89422 _89438 s f). Qed.
Lemma lem3452302 {_89422 _89438 : Type'} : term296 _89422 _89438.
Proof. exact (fun f : type1470 _89422 _89438 => @lem3452297 _89422 _89438 f). Qed.
