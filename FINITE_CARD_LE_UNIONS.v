Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_CARD_LE_UNIONS_term_abbrevs.
Require Import CARD_UNIONS_LE_spec.
Require Import FINITE_IMAGE_spec.
Require Import FINITE_UNIONS_spec.
Require Import FORALL_IN_GSPEC_spec.
Require Import HAS_SIZE_spec.
Require Import LE_MULT_RCANCEL_spec.
Require Import LE_TRANS_spec.
Require Import SIMPLE_IMAGE_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1831_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem4605903 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem4605904 {A B : Type'} (s : A -> Prop) (h1 : term0 A B) : term1 A B s.
Proof. exact (@lem4605903 A B h1 s). Qed.
Lemma lem4605905 {A B : Type'} (s : A -> Prop) : (term1 A B s) = (term2 A B s).
Proof. exact (eq_refl (term1 A B s)). Qed.
Lemma lem4605906 {A B : Type'} (s : A -> Prop) (h1 : term0 A B) : term2 A B s.
Proof. exact (EQ_MP (@lem4605905 A B s) (@lem4605904 A B s h1)). Qed.
Lemma lem4605907 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (h1 : term0 A B) : term3 A B s t.
Proof. exact (@lem4605906 A B s h1 t). Qed.
Lemma lem4605908 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term3 A B s t) = (term4 A B s t).
Proof. exact (eq_refl (term3 A B s t)). Qed.
Lemma lem4605909 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (h1 : term0 A B) : term4 A B s t.
Proof. exact (EQ_MP (@lem4605908 A B s t) (@lem4605907 A B s t h1)). Qed.
Lemma lem4605910 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (h1 : term0 A B) : term5 A B s t m.
Proof. exact (@lem4605909 A B s t h1 m). Qed.
Lemma lem4605911 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term5 A B s t m) = (term6 A B s t m).
Proof. exact (eq_refl (term5 A B s t m)). Qed.
Lemma lem4605912 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (h1 : term0 A B) : term6 A B s t m.
Proof. exact (EQ_MP (@lem4605911 A B s t m) (@lem4605910 A B s t m h1)). Qed.
Lemma lem4605913 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) (h1 : term0 A B) : term7 A B s t m n.
Proof. exact (@lem4605912 A B s t m h1 n). Qed.
Lemma lem4605914 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term7 A B s t m n) = (term8 A B s t m n).
Proof. exact (eq_refl (term7 A B s t m n)). Qed.
Lemma lem4605915 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) (h1 : term0 A B) : term8 A B s t m n.
Proof. exact (EQ_MP (@lem4605914 A B s t m n) (@lem4605913 A B s t m n h1)). Qed.
Lemma lem4605916 {A B : Type'} (m : nat) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term9 A B m s t n) : term9 A B m s t n.
Proof. exact (h1). Qed.
Lemma lem4605917 {A B : Type'} (m : nat) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term0 A B) (h2 : term9 A B m s t n) : term10 A B s t m n.
Proof. exact (@lem4605915 A B s t m n h1 (@lem4605916 A B m s t n h2)). Qed.
Lemma lem4605918 {A B : Type'} (m : nat) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term9 A B m s t n) : term11 A B s t m n.
Proof. exact (fun h0 : term0 A B => @lem4605917 A B m s t n h0 h1). Qed.
Lemma lem4605919 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem4605920 {A B : Type'} (m : nat) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term0 A B) (h2 : term9 A B m s t n) : term10 A B s t m n.
Proof. exact (@lem4605918 A B m s t n h2 (@lem4605919 A B h1)). Qed.
Lemma lem4605921 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) (h1 : term0 A B) : term8 A B s t m n.
Proof. exact (fun h0 : term9 A B m s t n => @lem4605920 A B m s t n h1 h0). Qed.
Lemma lem4605922 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (h1 : term0 A B) : term6 A B s t m.
Proof. exact (fun n : nat => @lem4605921 A B s t m n h1). Qed.
Lemma lem4605923 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (h1 : term0 A B) : term4 A B s t.
Proof. exact (fun m : nat => @lem4605922 A B s t m h1). Qed.
Lemma lem4605924 {A B : Type'} (s : A -> Prop) (h1 : term0 A B) : term2 A B s.
Proof. exact (fun t : type1413 A B => @lem4605923 A B s t h1). Qed.
Lemma lem4605925 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (fun s : A -> Prop => @lem4605924 A B s h1). Qed.
Lemma lem4605926 {A B : Type'} : term12 A B.
Proof. exact (fun h0 : term0 A B => @lem4605925 A B h0). Qed.
Lemma lem4605927 {A B : Type'} : term0 A B.
Proof. exact (@lem4605926 A B (@lem3934511 A B)). Qed.
Lemma lem4605928 {A B : Type'} (s : A -> Prop) : term1 A B s.
Proof. exact (@lem4605927 A B s). Qed.
Lemma lem4605929 {A B : Type'} (s : A -> Prop) : (term1 A B s) = (term2 A B s).
Proof. exact (eq_refl (term1 A B s)). Qed.
Lemma lem4605930 {A B : Type'} (s : A -> Prop) : term2 A B s.
Proof. exact (EQ_MP (@lem4605929 A B s) (@lem4605928 A B s)). Qed.
Lemma lem4605931 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : term3 A B s t.
Proof. exact (@lem4605930 A B s t). Qed.
Lemma lem4605932 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term3 A B s t) = (term4 A B s t).
Proof. exact (eq_refl (term3 A B s t)). Qed.
Lemma lem4605933 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : term4 A B s t.
Proof. exact (EQ_MP (@lem4605932 A B s t) (@lem4605931 A B s t)). Qed.
Lemma lem4605934 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : term5 A B s t m.
Proof. exact (@lem4605933 A B s t m). Qed.
Lemma lem4605935 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term5 A B s t m) = (term6 A B s t m).
Proof. exact (eq_refl (term5 A B s t m)). Qed.
Lemma lem4605936 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : term6 A B s t m.
Proof. exact (EQ_MP (@lem4605935 A B s t m) (@lem4605934 A B s t m)). Qed.
Lemma lem4605937 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : term7 A B s t m n.
Proof. exact (@lem4605936 A B s t m n). Qed.
Lemma lem4605938 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term7 A B s t m n) = (term8 A B s t m n).
Proof. exact (eq_refl (term7 A B s t m n)). Qed.
Lemma lem4605942 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) (h1 : (term13 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s)) : (term13 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s).
Proof. exact (h1). Qed.
Lemma lem4605943 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) (h1 : (term13 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s)) : (@IMAGE _88128 _88132 f s) = (term13 _88128 _88132 s f).
Proof. exact (SYM (@lem4605942 _88128 _88132 f s h1)). Qed.
Lemma lem4605944 {_88128 _88132 : Type'} (s : _88128 -> Prop) (f : _88128 -> _88132) (h1 : (@IMAGE _88128 _88132 f s) = (term13 _88128 _88132 s f)) : (@IMAGE _88128 _88132 f s) = (term13 _88128 _88132 s f).
Proof. exact (h1). Qed.
Lemma lem4605945 {_88128 _88132 : Type'} (s : _88128 -> Prop) (f : _88128 -> _88132) (h1 : (@IMAGE _88128 _88132 f s) = (term13 _88128 _88132 s f)) : (term13 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s).
Proof. exact (SYM (@lem4605944 _88128 _88132 s f h1)). Qed.
Lemma lem4605946 {_88128 _88132 : Type'} (s : _88128 -> Prop) (f : _88128 -> _88132) : ((term13 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s)) = ((@IMAGE _88128 _88132 f s) = (term13 _88128 _88132 s f)).
Proof. exact (prop_ext (fun h1 : (term13 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s) => @lem4605943 _88128 _88132 f s h1) (fun h1 : (@IMAGE _88128 _88132 f s) = (term13 _88128 _88132 s f) => @lem4605945 _88128 _88132 s f h1)). Qed.
Lemma lem4605947 {_88128 _88132 : Type'} (f : _88128 -> _88132) : (term14 _88128 _88132 f) = (term15 _88128 _88132 f).
Proof. exact (fun_ext (fun s : _88128 -> Prop => @lem4605946 _88128 _88132 s f)). Qed.
Lemma lem4605948 {_88128 : Type'} : (@all (_88128 -> Prop)) = (@all (_88128 -> Prop)).
Proof. exact (eq_refl (@all (_88128 -> Prop))). Qed.
Lemma lem4605949 {_88128 _88132 : Type'} (f : _88128 -> _88132) : (term16 _88128 _88132 f) = (term17 _88128 _88132 f).
Proof. exact (MK_COMB (@lem4605948 _88128) (@lem4605947 _88128 _88132 f)). Qed.
Lemma lem4605950 {_88128 _88132 : Type'} : (term18 _88128 _88132) = (term19 _88128 _88132).
Proof. exact (fun_ext (fun f : _88128 -> _88132 => @lem4605949 _88128 _88132 f)). Qed.
Lemma lem4605951 {_88128 _88132 : Type'} : (@all (_88128 -> _88132)) = (@all (_88128 -> _88132)).
Proof. exact (eq_refl (@all (_88128 -> _88132))). Qed.
Lemma lem4605952 {_88128 _88132 : Type'} : (term20 _88128 _88132) = (term21 _88128 _88132).
Proof. exact (MK_COMB (@lem4605951 _88128 _88132) (@lem4605950 _88128 _88132)). Qed.
Lemma lem4605953 {_88128 _88132 : Type'} : term21 _88128 _88132.
Proof. exact (EQ_MP (@lem4605952 _88128 _88132) (@lem3393993 _88128 _88132)). Qed.
Lemma lem4605954 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term22 A B t n s m) : term22 A B t n s m.
Proof. exact (h1). Qed.
Lemma lem4605955 {A : Type'} (s : A -> Prop) (m : nat) (h1 : term23 A s m) : term23 A s m.
Proof. exact (h1). Qed.
Lemma lem4605956 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term24 A B s t n) : term24 A B s t n.
Proof. exact (h1). Qed.
Lemma lem4605957 {A : Type'} (s : A -> Prop) (m : nat) (h1 : term25 A s m) : term25 A s m.
Proof. exact (h1). Qed.
Lemma lem4605958 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4605959 {_88128 _88132 : Type'} (f : _88128 -> _88132) : term26 _88128 _88132 f.
Proof. exact (@lem3393993 _88128 _88132 f). Qed.
Lemma lem4605960 {_88128 _88132 : Type'} (f : _88128 -> _88132) : (term26 _88128 _88132 f) = (term16 _88128 _88132 f).
Proof. exact (eq_refl (term26 _88128 _88132 f)). Qed.
Lemma lem4605961 {_88128 _88132 : Type'} (f : _88128 -> _88132) : term16 _88128 _88132 f.
Proof. exact (EQ_MP (@lem4605960 _88128 _88132 f) (@lem4605959 _88128 _88132 f)). Qed.
Lemma lem4605962 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : term27 _88128 _88132 f s.
Proof. exact (@lem4605961 _88128 _88132 f s). Qed.
Lemma lem4605963 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : (term27 _88128 _88132 f s) = ((term13 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s)).
Proof. exact (eq_refl (term27 _88128 _88132 f s)). Qed.
Lemma lem4605965 {A B : Type'} (f : A -> B) : term28 A B f.
Proof. exact (@lem3615104 A B f). Qed.
Lemma lem4605966 {A B : Type'} (f : A -> B) : (term28 A B f) = (term29 A B f).
Proof. exact (eq_refl (term28 A B f)). Qed.
Lemma lem4605967 {A B : Type'} (f : A -> B) : term29 A B f.
Proof. exact (EQ_MP (@lem4605966 A B f) (@lem4605965 A B f)). Qed.
Lemma lem4605968 {A B : Type'} (f : A -> B) (s : A -> Prop) : term30 A B f s.
Proof. exact (@lem4605967 A B f s). Qed.
Lemma lem4605969 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term30 A B f s) = (term31 A B f s).
Proof. exact (eq_refl (term30 A B f s)). Qed.
Lemma lem4605970 {A B : Type'} (f : A -> B) (s : A -> Prop) : term31 A B f s.
Proof. exact (EQ_MP (@lem4605969 A B f s) (@lem4605968 A B f s)). Qed.
Lemma lem4605971 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4605972 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term32 A B f s.
Proof. exact (@lem4605970 A B f s (@lem4605971 A s h1)). Qed.
Lemma lem4605973 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term32 A B f s) = ((term32 A B f s) = True).
Proof. exact (@lem7 (term32 A B f s)). Qed.
Lemma lem4605974 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term32 A B f s) = True.
Proof. exact (EQ_MP (@lem4605973 A B f s) (@lem4605972 A B f s h1)). Qed.
Lemma lem4606003 {_88905 _89106 : Type'} (Q : _89106 -> Prop) : term33 _88905 _89106 Q.
Proof. exact (proj1 (@lem3435744 _88905 Prop Prop Prop Prop Prop _89106 Prop Prop Prop Prop Q)). Qed.
Lemma lem4606004 {_88905 _89106 : Type'} (Q : _89106 -> Prop) (P : _88905 -> Prop) : term34 _88905 _89106 Q P.
Proof. exact (@lem4606003 _88905 _89106 Q P). Qed.
Lemma lem4606005 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) : (term34 _88905 _89106 Q P) = (term35 _88905 _89106 P Q).
Proof. exact (eq_refl (term34 _88905 _89106 Q P)). Qed.
Lemma lem4606006 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) : term35 _88905 _89106 P Q.
Proof. exact (EQ_MP (@lem4606005 _88905 _89106 P Q) (@lem4606004 _88905 _89106 Q P)). Qed.
Lemma lem4606007 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) (f : _88905 -> _89106) : term36 _88905 _89106 P Q f.
Proof. exact (@lem4606006 _88905 _89106 P Q f). Qed.
Lemma lem4606008 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) (f : _88905 -> _89106) : (term36 _88905 _89106 P Q f) = ((term37 _88905 _89106 P f Q) = (term38 _88905 _89106 P Q f)).
Proof. exact (eq_refl (term36 _88905 _89106 P Q f)). Qed.
Lemma lem4606010 {A : Type'} (s : type686 A) : term39 A s.
Proof. exact (@lem4605902 A s). Qed.
Lemma lem4606011 {A : Type'} (s : type686 A) : (term39 A s) = ((term40 A s) = (term41 A s)).
Proof. exact (eq_refl (term39 A s)). Qed.
Lemma lem4606013 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term24 A B s t n) : term42 A B s t n x.
Proof. exact (@lem4605956 A B s t n h1 x). Qed.
Lemma lem4606014 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) (n : nat) : (term42 A B s t n x) = (term43 A B s t x n).
Proof. exact (eq_refl (term42 A B s t n x)). Qed.
Lemma lem4606015 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term24 A B s t n) : term43 A B s t x n.
Proof. exact (EQ_MP (@lem4606014 A B s t x n) (@lem4606013 A B x s t n h1)). Qed.
Lemma lem4606016 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem4606017 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term24 A B s t n) (h2 : @IN A x s) : term44 A B t x n.
Proof. exact (@lem4606015 A B x s t n h1 (@lem4606016 A x s h2)). Qed.
Lemma lem4606026 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term24 A B s t n) (h2 : @IN A x s) : term45 A B t x.
Proof. exact (proj1 (@lem4606017 A B t n x s h1 h2)). Qed.
Lemma lem4606027 {A B : Type'} (t : type1413 A B) (x : A) : (term45 A B t x) = ((term45 A B t x) = True).
Proof. exact (@lem7 (term45 A B t x)). Qed.
Lemma lem4606028 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term24 A B s t n) (h2 : @IN A x s) : (term45 A B t x) = True.
Proof. exact (EQ_MP (@lem4606027 A B t x) (@lem4606026 A B t n x s h1 h2)). Qed.
Lemma lem4606034 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem4606039 {A : Type'} (s : type686 A) : (term40 A s) = (term41 A s).
Proof. exact (EQ_MP (@lem4606011 A s) (@lem4606010 A s)). Qed.
Lemma lem4606040 {B : Type'} (s : type686 B) : (term40 B s) = (term41 B s).
Proof. exact (@lem4606039 B s). Qed.
Lemma lem4606041 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term46 A B s t) = (term47 A B s t).
Proof. exact (@lem4606040 B (term48 A B s t)). Qed.
Lemma lem4606045 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : (term13 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s).
Proof. exact (EQ_MP (@lem4605963 _88128 _88132 f s) (@lem4605962 _88128 _88132 f s)). Qed.
Lemma lem4606046 {A B : Type'} (f : type1413 A B) (s : A -> Prop) : (term48 A B s f) = (@IMAGE A (B -> Prop) f s).
Proof. exact (@lem4606045 A (B -> Prop) f s). Qed.
Lemma lem4606047 {A B : Type'} (t : type1413 A B) (s : A -> Prop) : (term48 A B s t) = (@IMAGE A (B -> Prop) t s).
Proof. exact (@lem4606046 A B t s). Qed.
Lemma lem4606048 {B : Type'} : (@FINITE (B -> Prop)) = (@FINITE (B -> Prop)).
Proof. exact (eq_refl (@FINITE (B -> Prop))). Qed.
Lemma lem4606049 {A B : Type'} (t : type1413 A B) (s : A -> Prop) : (term49 A B s t) = (term50 A B t s).
Proof. exact (MK_COMB (@lem4606048 B) (@lem4606047 A B t s)). Qed.
Lemma lem4606051 {A B : Type'} (f : A -> B) (s : A -> Prop) : term51 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem4605974 A B f s h0). Qed.
Lemma lem4606052 {A B : Type'} (f : type1413 A B) (s : A -> Prop) : term52 A B f s.
Proof. exact (@lem4606051 A (B -> Prop) f s). Qed.
Lemma lem4606053 {A B : Type'} (t : type1413 A B) (s : A -> Prop) : term52 A B t s.
Proof. exact (@lem4606052 A B t s). Qed.
Lemma lem4606055 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem4606034 A s) (@lem4605958 A s h1)). Qed.
Lemma lem4606056 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem4606055 A s h1)). Qed.
Lemma lem4606057 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem4606056 A s h1) (@lem0)). Qed.
Lemma lem4606058 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (h1 : @FINITE A s) : (term50 A B t s) = True.
Proof. exact (@lem4606053 A B t s (@lem4606057 A s h1)). Qed.
Lemma lem4606059 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (h1 : @FINITE A s) : (term49 A B s t) = True.
Proof. exact (TRANS (@lem4606049 A B t s) (@lem4606058 A B t s h1)). Qed.
Lemma lem4606060 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4606061 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (h1 : @FINITE A s) : (term53 A B s t) = (and True).
Proof. exact (MK_COMB (@lem4606060) (@lem4606059 A B t s h1)). Qed.
Lemma lem4606063 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) (f : _88905 -> _89106) : (term37 _88905 _89106 P f Q) = (term38 _88905 _89106 P Q f).
Proof. exact (EQ_MP (@lem4606008 _88905 _89106 P Q f) (@lem4606007 _88905 _89106 P Q f)). Qed.
Lemma lem4606064 {A B : Type'} (P : A -> Prop) (Q : type686 B) (f : type1413 A B) : (term54 A B P f Q) = (term55 A B P Q f).
Proof. exact (@lem4606063 A (B -> Prop) P Q f). Qed.
Lemma lem4606065 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term56 A B s t) = (term57 A B s t).
Proof. exact (@lem4606064 A B (term58 A s) (@FINITE B) t). Qed.
Lemma lem4606066 {A : Type'} (x : A) (s : A -> Prop) : (term59 A s x) = (@IN A x s).
Proof. exact (eq_refl (term59 A s x)). Qed.
Lemma lem4606067 {B : Type'} (GEN_PVAR_159 : B -> Prop) : (@SETSPEC (B -> Prop) GEN_PVAR_159) = (@SETSPEC (B -> Prop) GEN_PVAR_159).
Proof. exact (eq_refl (@SETSPEC (B -> Prop) GEN_PVAR_159)). Qed.
Lemma lem4606068 {A B : Type'} (GEN_PVAR_159 : B -> Prop) (x : A) (s : A -> Prop) : (term60 A B GEN_PVAR_159 s x) = (term61 A B GEN_PVAR_159 x s).
Proof. exact (MK_COMB (@lem4606067 B GEN_PVAR_159) (@lem4606066 A x s)). Qed.
Lemma lem4606069 {A B : Type'} (t : type1413 A B) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem4606070 {A B : Type'} (GEN_PVAR_159 : B -> Prop) (s : A -> Prop) (t : type1413 A B) (x : A) : (term62 A B GEN_PVAR_159 s t x) = (term63 A B GEN_PVAR_159 s t x).
Proof. exact (MK_COMB (@lem4606068 A B GEN_PVAR_159 x s) (@lem4606069 A B t x)). Qed.
Lemma lem4606071 {A B : Type'} (GEN_PVAR_159 : B -> Prop) (s : A -> Prop) (t : type1413 A B) : (term64 A B GEN_PVAR_159 s t) = (term65 A B GEN_PVAR_159 s t).
Proof. exact (fun_ext (fun x : A => @lem4606070 A B GEN_PVAR_159 s t x)). Qed.
Lemma lem4606072 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4606073 {A B : Type'} (GEN_PVAR_159 : B -> Prop) (s : A -> Prop) (t : type1413 A B) : (term66 A B GEN_PVAR_159 s t) = (term67 A B GEN_PVAR_159 s t).
Proof. exact (MK_COMB (@lem4606072 A) (@lem4606071 A B GEN_PVAR_159 s t)). Qed.
Lemma lem4606074 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term68 A B s t) = (term69 A B s t).
Proof. exact (fun_ext (fun GEN_PVAR_159 : B -> Prop => @lem4606073 A B GEN_PVAR_159 s t)). Qed.
Lemma lem4606075 {B : Type'} : (@GSPEC (B -> Prop)) = (@GSPEC (B -> Prop)).
Proof. exact (eq_refl (@GSPEC (B -> Prop))). Qed.
Lemma lem4606076 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term70 A B s t) = (term48 A B s t).
Proof. exact (MK_COMB (@lem4606075 B) (@lem4606074 A B s t)). Qed.
Lemma lem4606077 {B : Type'} (t : B -> Prop) : (@IN (B -> Prop) t) = (@IN (B -> Prop) t).
Proof. exact (eq_refl (@IN (B -> Prop) t)). Qed.
Lemma lem4606078 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : type1413 A B) : (term71 A B t s t') = (term72 A B t s t').
Proof. exact (MK_COMB (@lem4606077 B t) (@lem4606076 A B s t')). Qed.
Lemma lem4606079 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4606080 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (t' : type1413 A B) : (term73 A B t s t') = (term74 A B t s t').
Proof. exact (MK_COMB (@lem4606079) (@lem4606078 A B t s t')). Qed.
Lemma lem4606081 {B : Type'} (t : B -> Prop) : (@FINITE B t) = (@FINITE B t).
Proof. exact (eq_refl (@FINITE B t)). Qed.
Lemma lem4606082 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (t' : B -> Prop) : (term75 A B s t t') = (term76 A B s t t').
Proof. exact (MK_COMB (@lem4606080 A B t' s t) (@lem4606081 B t')). Qed.
Lemma lem4606083 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term77 A B s t) = (term78 A B s t).
Proof. exact (fun_ext (fun t' : B -> Prop => @lem4606082 A B s t t')). Qed.
Lemma lem4606084 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4606085 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term56 A B s t) = (term79 A B s t).
Proof. exact (MK_COMB (@lem4606084 B) (@lem4606083 A B s t)). Qed.
Lemma lem4606086 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4606087 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term80 A B s t) = (term81 A B s t).
Proof. exact (MK_COMB (@lem4606086) (@lem4606085 A B s t)). Qed.
Lemma lem4606088 {A : Type'} (x : A) (s : A -> Prop) : (term59 A s x) = (@IN A x s).
Proof. exact (eq_refl (term59 A s x)). Qed.
Lemma lem4606089 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4606090 {A : Type'} (x : A) (s : A -> Prop) : (term82 A s x) = (term83 A x s).
Proof. exact (MK_COMB (@lem4606089) (@lem4606088 A x s)). Qed.
Lemma lem4606091 {A B : Type'} (t : type1413 A B) (x : A) : (term45 A B t x) = (term45 A B t x).
Proof. exact (eq_refl (term45 A B t x)). Qed.
Lemma lem4606092 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) : (term84 A B s t x) = (term85 A B s t x).
Proof. exact (MK_COMB (@lem4606090 A x s) (@lem4606091 A B t x)). Qed.
Lemma lem4606093 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term86 A B s t) = (term87 A B s t).
Proof. exact (fun_ext (fun x : A => @lem4606092 A B s t x)). Qed.
Lemma lem4606094 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4606095 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term57 A B s t) = (term88 A B s t).
Proof. exact (MK_COMB (@lem4606094 A) (@lem4606093 A B s t)). Qed.
Lemma lem4606096 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : ((term56 A B s t) = (term57 A B s t)) = ((term79 A B s t) = (term88 A B s t)).
Proof. exact (MK_COMB (@lem4606087 A B s t) (@lem4606095 A B s t)). Qed.
Lemma lem4606097 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term79 A B s t) = (term88 A B s t).
Proof. exact (EQ_MP (@lem4606096 A B s t) (@lem4606065 A B s t)). Qed.
Lemma lem4606105 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term89 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4606106 (p : Prop) (q : Prop) (p' : Prop) : term90 p q p'.
Proof. exact (fun q' : Prop => @lem4606105 p q p' q'). Qed.
Lemma lem4606107 (p : Prop) (q : Prop) : term91 p q.
Proof. exact (fun p' : Prop => @lem4606106 p q p'). Qed.
Lemma lem4606108 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) : term92 A B s t x.
Proof. exact (@lem4606107 (@IN A x s) (term45 A B t x)). Qed.
Lemma lem4606109 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) (p' : Prop) : term93 A B s t x p'.
Proof. exact (@lem4606108 A B s t x p'). Qed.
Lemma lem4606110 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) (p' : Prop) : (term93 A B s t x p') = (term94 A B s t x p').
Proof. exact (eq_refl (term93 A B s t x p')). Qed.
Lemma lem4606111 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) (p' : Prop) : term94 A B s t x p'.
Proof. exact (EQ_MP (@lem4606110 A B s t x p') (@lem4606109 A B s t x p')). Qed.
Lemma lem4606112 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) (p' : Prop) (q' : Prop) : term95 A B s t x p' q'.
Proof. exact (@lem4606111 A B s t x p' q'). Qed.
Lemma lem4606113 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) (p' : Prop) (q' : Prop) : (term95 A B s t x p' q') = (term96 A B s t x p' q').
Proof. exact (eq_refl (term95 A B s t x p' q')). Qed.
Lemma lem4606114 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) (p' : Prop) (q' : Prop) : term96 A B s t x p' q'.
Proof. exact (EQ_MP (@lem4606113 A B s t x p' q') (@lem4606112 A B s t x p' q')). Qed.
Lemma lem4606115 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem4606116 {A B : Type'} (t : type1413 A B) (x : A) (s : A -> Prop) (q' : Prop) : term97 A B t x s q'.
Proof. exact (@lem4606114 A B s t x (@IN A x s) q'). Qed.
Lemma lem4606117 {A B : Type'} (t : type1413 A B) (x : A) (s : A -> Prop) (q' : Prop) : term98 A B t x s q'.
Proof. exact (@lem4606116 A B t x s q' (@lem4606115 A x s)). Qed.
Lemma lem4606118 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem4606119 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem4606122 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term24 A B s t n) : term99 A B s t x.
Proof. exact (fun h0 : @IN A x s => @lem4606028 A B t n x s h1 h0). Qed.
Lemma lem4606123 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term24 A B s t n) : term99 A B s t x.
Proof. exact (@lem4606122 A B x s t n h1). Qed.
Lemma lem4606125 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem4606119 A x s) (@lem4606118 A x s h1)). Qed.
Lemma lem4606126 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : True = (@IN A x s).
Proof. exact (SYM (@lem4606125 A x s h1)). Qed.
Lemma lem4606127 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (EQ_MP (@lem4606126 A x s h1) (@lem0)). Qed.
Lemma lem4606128 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term24 A B s t n) (h2 : @IN A x s) : (term45 A B t x) = True.
Proof. exact (@lem4606123 A B x s t n h1 (@lem4606127 A x s h2)). Qed.
Lemma lem4606129 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term24 A B s t n) : term99 A B s t x.
Proof. exact (fun h0 : @IN A x s => @lem4606128 A B t n x s h1 h0). Qed.
Lemma lem4606130 {A B : Type'} (t : type1413 A B) (x : A) (s : A -> Prop) : term100 A B t x s.
Proof. exact (@lem4606117 A B t x s True). Qed.
Lemma lem4606131 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term24 A B s t n) : (term85 A B s t x) = (term101 A x s).
Proof. exact (@lem4606130 A B t x s (@lem4606129 A B x s t n h1)). Qed.
Lemma lem4606133 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4606134 {A : Type'} (x : A) (s : A -> Prop) : (term101 A x s) = True.
Proof. exact (@lem4606133 (@IN A x s)). Qed.
Lemma lem4606135 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term24 A B s t n) : (term85 A B s t x) = True.
Proof. exact (TRANS (@lem4606131 A B x s t n h1) (@lem4606134 A x s)). Qed.
Lemma lem4606136 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term24 A B s t n) : (term87 A B s t) = (term102 A).
Proof. exact (fun_ext (fun x : A => @lem4606135 A B x s t n h1)). Qed.
Lemma lem4606137 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4606138 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term24 A B s t n) : (term88 A B s t) = (term103 A).
Proof. exact (MK_COMB (@lem4606137 A) (@lem4606136 A B s t n h1)). Qed.
Lemma lem4606140 {A : Type'} (t : Prop) : (term104 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4606141 {A : Type'} (t : Prop) : (term104 A t) = t.
Proof. exact (@lem4606140 A t). Qed.
Lemma lem4606142 {A : Type'} : (term103 A) = True.
Proof. exact (@lem4606141 A True). Qed.
Lemma lem4606143 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term24 A B s t n) : (term88 A B s t) = True.
Proof. exact (TRANS (@lem4606138 A B s t n h1) (@lem4606142 A)). Qed.
Lemma lem4606144 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term24 A B s t n) : (term79 A B s t) = True.
Proof. exact (TRANS (@lem4606097 A B s t) (@lem4606143 A B s t n h1)). Qed.
Lemma lem4606145 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (h1 : term24 A B s t n) (h2 : @FINITE A s) : (term47 A B s t) = (True /\ True).
Proof. exact (MK_COMB (@lem4606061 A B t s h2) (@lem4606144 A B s t n h1)). Qed.
Lemma lem4606147 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4606148 : (True /\ True) = True.
Proof. exact (@lem4606147 True). Qed.
Lemma lem4606149 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (h1 : term24 A B s t n) (h2 : @FINITE A s) : (term47 A B s t) = True.
Proof. exact (TRANS (@lem4606145 A B t n s h1 h2) (@lem4606148)). Qed.
Lemma lem4606150 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (h1 : term24 A B s t n) (h2 : @FINITE A s) : (term46 A B s t) = True.
Proof. exact (TRANS (@lem4606041 A B s t) (@lem4606149 A B t n s h1 h2)). Qed.
Lemma lem4606151 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (h1 : term24 A B s t n) (h2 : @FINITE A s) : True = (term46 A B s t).
Proof. exact (SYM (@lem4606150 A B t n s h1 h2)). Qed.
Lemma lem4606152 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (h1 : term24 A B s t n) (h2 : @FINITE A s) : term46 A B s t.
Proof. exact (EQ_MP (@lem4606151 A B t n s h1 h2) (@lem0)). Qed.
Lemma lem4606153 {_88128 _88132 : Type'} (f : _88128 -> _88132) : term26 _88128 _88132 f.
Proof. exact (@lem3393993 _88128 _88132 f). Qed.
Lemma lem4606154 {_88128 _88132 : Type'} (f : _88128 -> _88132) : (term26 _88128 _88132 f) = (term16 _88128 _88132 f).
Proof. exact (eq_refl (term26 _88128 _88132 f)). Qed.
Lemma lem4606155 {_88128 _88132 : Type'} (f : _88128 -> _88132) : term16 _88128 _88132 f.
Proof. exact (EQ_MP (@lem4606154 _88128 _88132 f) (@lem4606153 _88128 _88132 f)). Qed.
Lemma lem4606156 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : term27 _88128 _88132 f s.
Proof. exact (@lem4606155 _88128 _88132 f s). Qed.
Lemma lem4606157 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : (term27 _88128 _88132 f s) = ((term13 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s)).
Proof. exact (eq_refl (term27 _88128 _88132 f s)). Qed.
Lemma lem4606233 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : (term13 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s).
Proof. exact (EQ_MP (@lem4606157 _88128 _88132 f s) (@lem4606156 _88128 _88132 f s)). Qed.
Lemma lem4606234 {A B : Type'} (f : type1413 A B) (s : A -> Prop) : (term48 A B s f) = (@IMAGE A (B -> Prop) f s).
Proof. exact (@lem4606233 A (B -> Prop) f s). Qed.
Lemma lem4606235 {A B : Type'} (t : type1413 A B) (s : A -> Prop) : (term48 A B s t) = (@IMAGE A (B -> Prop) t s).
Proof. exact (@lem4606234 A B t s). Qed.
Lemma lem4606236 {B : Type'} : (@UNIONS B) = (@UNIONS B).
Proof. exact (eq_refl (@UNIONS B)). Qed.
Lemma lem4606237 {A B : Type'} (t : type1413 A B) (s : A -> Prop) : (term105 A B s t) = (term106 A B t s).
Proof. exact (MK_COMB (@lem4606236 B) (@lem4606235 A B t s)). Qed.
Lemma lem4606238 {B : Type'} : (@CARD B) = (@CARD B).
Proof. exact (eq_refl (@CARD B)). Qed.
Lemma lem4606239 {A B : Type'} (t : type1413 A B) (s : A -> Prop) : (term107 A B s t) = (term108 A B t s).
Proof. exact (MK_COMB (@lem4606238 B) (@lem4606237 A B t s)). Qed.
Lemma lem4606240 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem4606241 {A B : Type'} (t : type1413 A B) (s : A -> Prop) : (term109 A B s t) = (term110 A B t s).
Proof. exact (MK_COMB (@lem4606240) (@lem4606239 A B t s)). Qed.
Lemma lem4606242 (m : nat) (n : nat) : (Nat.mul m n) = (Nat.mul m n).
Proof. exact (eq_refl (Nat.mul m n)). Qed.
Lemma lem4606243 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (m : nat) (n : nat) : (term10 A B s t m n) = (term111 A B t s m n).
Proof. exact (MK_COMB (@lem4606241 A B t s) (@lem4606242 m n)). Qed.
Lemma lem4606244 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term111 A B t s m n) = (term10 A B s t m n).
Proof. exact (SYM (@lem4606243 A B t s m n)). Qed.
Lemma lem4606245 (h1 : term112) : term112.
Proof. exact (h1). Qed.
Lemma lem4606246 (m : nat) (h1 : term112) : term113 m.
Proof. exact (@lem4606245 h1 m). Qed.
Lemma lem4606247 (m : nat) : (term113 m) = (term114 m).
Proof. exact (eq_refl (term113 m)). Qed.
Lemma lem4606248 (m : nat) (h1 : term112) : term114 m.
Proof. exact (EQ_MP (@lem4606247 m) (@lem4606246 m h1)). Qed.
Lemma lem4606249 (m : nat) (n : nat) (h1 : term112) : term115 m n.
Proof. exact (@lem4606248 m h1 n). Qed.
Lemma lem4606250 (n : nat) (m : nat) : (term115 m n) = (term116 n m).
Proof. exact (eq_refl (term115 m n)). Qed.
Lemma lem4606251 (n : nat) (m : nat) (h1 : term112) : term116 n m.
Proof. exact (EQ_MP (@lem4606250 n m) (@lem4606249 m n h1)). Qed.
Lemma lem4606252 (n : nat) (m : nat) (p : nat) (h1 : term112) : term117 n m p.
Proof. exact (@lem4606251 n m h1 p). Qed.
Lemma lem4606253 (n : nat) (m : nat) (p : nat) : (term117 n m p) = (term118 n m p).
Proof. exact (eq_refl (term117 n m p)). Qed.
Lemma lem4606254 (n : nat) (m : nat) (p : nat) (h1 : term112) : term118 n m p.
Proof. exact (EQ_MP (@lem4606253 n m p) (@lem4606252 n m p h1)). Qed.
Lemma lem4606255 (m : nat) (n : nat) (p : nat) (h1 : term119 m n p) : term119 m n p.
Proof. exact (h1). Qed.
Lemma lem4606256 (m : nat) (n : nat) (p : nat) (h1 : term112) (h2 : term119 m n p) : Peano.le m p.
Proof. exact (@lem4606254 n m p h1 (@lem4606255 m n p h2)). Qed.
Lemma lem4606257 (m : nat) (n : nat) (p : nat) (h1 : term119 m n p) : term120 m p.
Proof. exact (fun h0 : term112 => @lem4606256 m n p h0 h1). Qed.
Lemma lem4606258 (m : nat) (p : nat) (h1 : term121 m p) : term121 m p.
Proof. exact (h1). Qed.
Lemma lem4606259 (m : nat) (p : nat) (h1 : term121 m p) : term120 m p.
Proof. exact (ex_elim (@lem4606258 m p h1) (fun n : nat => fun h0 : term122 m p n => @lem4606257 m n p h0)). Qed.
Lemma lem4606260 (h1 : term112) : term112.
Proof. exact (h1). Qed.
Lemma lem4606261 (m : nat) (p : nat) (h1 : term112) (h2 : term121 m p) : Peano.le m p.
Proof. exact (@lem4606259 m p h2 (@lem4606260 h1)). Qed.
Lemma lem4606262 (m : nat) (p : nat) (h1 : term112) : term123 m p.
Proof. exact (fun h0 : term121 m p => @lem4606261 m p h1 h0). Qed.
Lemma lem4606263 (m : nat) (h1 : term112) : term124 m.
Proof. exact (fun p : nat => @lem4606262 m p h1). Qed.
Lemma lem4606264 (h1 : term112) : term125.
Proof. exact (fun m : nat => @lem4606263 m h1). Qed.
Lemma lem4606265 : term126.
Proof. exact (fun h0 : term112 => @lem4606264 h0). Qed.
Lemma lem4606266 : term125.
Proof. exact (@lem4606265 (@lem93743)). Qed.
Lemma lem4606267 (m : nat) : term127 m.
Proof. exact (@lem4606266 m). Qed.
Lemma lem4606268 (m : nat) : (term127 m) = (term124 m).
Proof. exact (eq_refl (term127 m)). Qed.
Lemma lem4606269 (m : nat) : term124 m.
Proof. exact (EQ_MP (@lem4606268 m) (@lem4606267 m)). Qed.
Lemma lem4606270 (m : nat) (p : nat) : term128 m p.
Proof. exact (@lem4606269 m p). Qed.
Lemma lem4606271 (m : nat) (p : nat) : (term128 m p) = (term123 m p).
Proof. exact (eq_refl (term128 m p)). Qed.
Lemma lem4606274 (m : nat) (p : nat) : term123 m p.
Proof. exact (EQ_MP (@lem4606271 m p) (@lem4606270 m p)). Qed.
Lemma lem4606275 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (m : nat) (n : nat) : term129 A B t s m n.
Proof. exact (@lem4606274 (term108 A B t s) (Nat.mul m n)). Qed.
Lemma lem4606276 (m : nat) : term130 m.
Proof. exact (@lem104289 m). Qed.
Lemma lem4606277 (m : nat) : (term130 m) = (term131 m).
Proof. exact (eq_refl (term130 m)). Qed.
Lemma lem4606278 (m : nat) : term131 m.
Proof. exact (EQ_MP (@lem4606277 m) (@lem4606276 m)). Qed.
Lemma lem4606279 (m : nat) (n : nat) : term132 m n.
Proof. exact (@lem4606278 m n). Qed.
Lemma lem4606280 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (eq_refl (term132 m n)). Qed.
Lemma lem4606281 (m : nat) (n : nat) : term133 m n.
Proof. exact (EQ_MP (@lem4606280 m n) (@lem4606279 m n)). Qed.
Lemma lem4606282 (m : nat) (n : nat) (p : nat) : term134 m n p.
Proof. exact (@lem4606281 m n p). Qed.
Lemma lem4606283 (m : nat) (n : nat) (p : nat) : (term134 m n p) = ((term135 m n p) = (term136 m n p)).
Proof. exact (eq_refl (term134 m n p)). Qed.
Lemma lem4606285 {_88128 _88132 : Type'} (f : _88128 -> _88132) : term137 _88128 _88132 f.
Proof. exact (@lem4605953 _88128 _88132 f). Qed.
Lemma lem4606286 {_88128 _88132 : Type'} (f : _88128 -> _88132) : (term137 _88128 _88132 f) = (term17 _88128 _88132 f).
Proof. exact (eq_refl (term137 _88128 _88132 f)). Qed.
Lemma lem4606287 {_88128 _88132 : Type'} (f : _88128 -> _88132) : term17 _88128 _88132 f.
Proof. exact (EQ_MP (@lem4606286 _88128 _88132 f) (@lem4606285 _88128 _88132 f)). Qed.
Lemma lem4606288 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : term138 _88128 _88132 f s.
Proof. exact (@lem4606287 _88128 _88132 f s). Qed.
Lemma lem4606289 {_88128 _88132 : Type'} (s : _88128 -> Prop) (f : _88128 -> _88132) : (term138 _88128 _88132 f s) = ((@IMAGE _88128 _88132 f s) = (term13 _88128 _88132 s f)).
Proof. exact (eq_refl (term138 _88128 _88132 f s)). Qed.
Lemma lem4606298 {A : Type'} (s : A -> Prop) (m : nat) : (term25 A s m) = ((term25 A s m) = True).
Proof. exact (@lem7 (term25 A s m)). Qed.
Lemma lem4606303 {_88128 _88132 : Type'} (s : _88128 -> Prop) (f : _88128 -> _88132) : (@IMAGE _88128 _88132 f s) = (term13 _88128 _88132 s f).
Proof. exact (EQ_MP (@lem4606289 _88128 _88132 s f) (@lem4606288 _88128 _88132 f s)). Qed.
Lemma lem4606304 {A B : Type'} (s : A -> Prop) (f : type1413 A B) : (@IMAGE A (B -> Prop) f s) = (term48 A B s f).
Proof. exact (@lem4606303 A (B -> Prop) s f). Qed.
Lemma lem4606305 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (@IMAGE A (B -> Prop) t s) = (term48 A B s t).
Proof. exact (@lem4606304 A B s t). Qed.
Lemma lem4606310 {B : Type'} : (@UNIONS B) = (@UNIONS B).
Proof. exact (eq_refl (@UNIONS B)). Qed.
Lemma lem4606311 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term106 A B t s) = (term105 A B s t).
Proof. exact (MK_COMB (@lem4606310 B) (@lem4606305 A B s t)). Qed.
Lemma lem4606312 {B : Type'} : (@CARD B) = (@CARD B).
Proof. exact (eq_refl (@CARD B)). Qed.
Lemma lem4606313 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term108 A B t s) = (term107 A B s t).
Proof. exact (MK_COMB (@lem4606312 B) (@lem4606311 A B s t)). Qed.
Lemma lem4606314 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem4606315 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term110 A B t s) = (term109 A B s t).
Proof. exact (MK_COMB (@lem4606314) (@lem4606313 A B s t)). Qed.
Lemma lem4606316 {A : Type'} (s : A -> Prop) (n : nat) : (term139 A s n) = (term139 A s n).
Proof. exact (eq_refl (term139 A s n)). Qed.
Lemma lem4606317 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (n : nat) : (term140 A B t s n) = (term141 A B t s n).
Proof. exact (MK_COMB (@lem4606315 A B s t) (@lem4606316 A s n)). Qed.
Lemma lem4606318 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4606319 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (n : nat) : (term142 A B t s n) = (term143 A B t s n).
Proof. exact (MK_COMB (@lem4606318) (@lem4606317 A B t s n)). Qed.
Lemma lem4606321 (m : nat) (n : nat) (p : nat) : (term135 m n p) = (term136 m n p).
Proof. exact (EQ_MP (@lem4606283 m n p) (@lem4606282 m n p)). Qed.
Lemma lem4606322 {A : Type'} (s : A -> Prop) (m : nat) (n : nat) : (term144 A s m n) = (term145 A s m n).
Proof. exact (@lem4606321 (@CARD A s) m n). Qed.
Lemma lem4606326 {A : Type'} (s : A -> Prop) (m : nat) (h1 : term25 A s m) : (term25 A s m) = True.
Proof. exact (EQ_MP (@lem4606298 A s m) (@lem4605957 A s m h1)). Qed.
Lemma lem4606327 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4606328 {A : Type'} (s : A -> Prop) (m : nat) (h1 : term25 A s m) : (term146 A s m) = (or True).
Proof. exact (MK_COMB (@lem4606327) (@lem4606326 A s m h1)). Qed.
Lemma lem4606331 (n : nat) : (n = (NUMERAL 0)) = (n = (NUMERAL 0)).
Proof. exact (eq_refl (n = (NUMERAL 0))). Qed.
Lemma lem4606332 {A : Type'} (n : nat) (s : A -> Prop) (m : nat) (h1 : term25 A s m) : (term145 A s m n) = (term147 n).
Proof. exact (MK_COMB (@lem4606328 A s m h1) (@lem4606331 n)). Qed.
Lemma lem4606334 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem4606335 (n : nat) : (term147 n) = True.
Proof. exact (@lem4606334 (n = (NUMERAL 0))). Qed.
Lemma lem4606336 {A : Type'} (n : nat) (s : A -> Prop) (m : nat) (h1 : term25 A s m) : (term145 A s m n) = True.
Proof. exact (TRANS (@lem4606332 A n s m h1) (@lem4606335 n)). Qed.
Lemma lem4606337 {A : Type'} (n : nat) (s : A -> Prop) (m : nat) (h1 : term25 A s m) : (term144 A s m n) = True.
Proof. exact (TRANS (@lem4606322 A s m n) (@lem4606336 A n s m h1)). Qed.
Lemma lem4606338 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term25 A s m) : (term148 A B t s m n) = (term149 A B t s n).
Proof. exact (MK_COMB (@lem4606319 A B t s n) (@lem4606337 A n s m h1)). Qed.
Lemma lem4606340 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4606341 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (n : nat) : (term149 A B t s n) = (term141 A B t s n).
Proof. exact (@lem4606340 (term141 A B t s n)). Qed.
Lemma lem4606346 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term25 A s m) : (term148 A B t s m n) = (term141 A B t s n).
Proof. exact (TRANS (@lem4606338 A B t n s m h1) (@lem4606341 A B t s n)). Qed.
Lemma lem4606347 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term25 A s m) : (term141 A B t s n) = (term148 A B t s m n).
Proof. exact (SYM (@lem4606346 A B t n s m h1)). Qed.
Lemma lem4606349 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : term8 A B s t m n.
Proof. exact (EQ_MP (@lem4605938 A B s t m n) (@lem4605937 A B s t m n)). Qed.
Lemma lem4606350 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : term8 A B s t m n.
Proof. exact (@lem4606349 A B s t m n). Qed.
Lemma lem4606351 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (n : nat) : term150 A B t s n.
Proof. exact (@lem4606350 A B s t (@CARD A s) n). Qed.
Lemma lem4606352 {_100044 : Type'} (s : _100044 -> Prop) : term151 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem4606353 {_100044 : Type'} (s : _100044 -> Prop) : (term151 _100044 s) = (term152 _100044 s).
Proof. exact (eq_refl (term151 _100044 s)). Qed.
Lemma lem4606354 {_100044 : Type'} (s : _100044 -> Prop) : term152 _100044 s.
Proof. exact (EQ_MP (@lem4606353 _100044 s) (@lem4606352 _100044 s)). Qed.
Lemma lem4606355 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term153 _100044 s n.
Proof. exact (@lem4606354 _100044 s n). Qed.
Lemma lem4606356 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term153 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term154 _100044 s n)).
Proof. exact (eq_refl (term153 _100044 s n)). Qed.
Lemma lem4606358 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term24 A B s t n) : term42 A B s t n x.
Proof. exact (@lem4605956 A B s t n h1 x). Qed.
Lemma lem4606359 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) (n : nat) : (term42 A B s t n x) = (term43 A B s t x n).
Proof. exact (eq_refl (term42 A B s t n x)). Qed.
Lemma lem4606360 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term24 A B s t n) : term43 A B s t x n.
Proof. exact (EQ_MP (@lem4606359 A B s t x n) (@lem4606358 A B x s t n h1)). Qed.
Lemma lem4606361 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) (n : nat) : (term43 A B s t x n) = ((term43 A B s t x n) = True).
Proof. exact (@lem7 (term43 A B s t x n)). Qed.
Lemma lem4606363 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem4606370 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term154 _100044 s n).
Proof. exact (EQ_MP (@lem4606356 _100044 s n) (@lem4606355 _100044 s n)). Qed.
Lemma lem4606371 {A : Type'} (s : A -> Prop) (n : nat) : (@HAS_SIZE A s n) = (term154 A s n).
Proof. exact (@lem4606370 A s n). Qed.
Lemma lem4606372 {A : Type'} (s : A -> Prop) : (term155 A s) = (term156 A s).
Proof. exact (@lem4606371 A s (@CARD A s)). Qed.
Lemma lem4606376 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem4606363 A s) (@lem4605958 A s h1)). Qed.
Lemma lem4606377 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4606378 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term157 A s) = (and True).
Proof. exact (MK_COMB (@lem4606377) (@lem4606376 A s h1)). Qed.
Lemma lem4606380 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4606381 (x : nat) : (x = x) = True.
Proof. exact (@lem4606380 nat x). Qed.
Lemma lem4606382 {A : Type'} (s : A -> Prop) : ((@CARD A s) = (@CARD A s)) = True.
Proof. exact (@lem4606381 (@CARD A s)). Qed.
Lemma lem4606383 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term156 A s) = (True /\ True).
Proof. exact (MK_COMB (@lem4606378 A s h1) (@lem4606382 A s)). Qed.
Lemma lem4606385 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4606386 : (True /\ True) = True.
Proof. exact (@lem4606385 True). Qed.
Lemma lem4606387 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term156 A s) = True.
Proof. exact (TRANS (@lem4606383 A s h1) (@lem4606386)). Qed.
Lemma lem4606388 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term155 A s) = True.
Proof. exact (TRANS (@lem4606372 A s) (@lem4606387 A s h1)). Qed.
Lemma lem4606389 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4606390 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term158 A s) = (and True).
Proof. exact (MK_COMB (@lem4606389) (@lem4606388 A s h1)). Qed.
Lemma lem4606396 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term24 A B s t n) : (term43 A B s t x n) = True.
Proof. exact (EQ_MP (@lem4606361 A B s t x n) (@lem4606360 A B x s t n h1)). Qed.
Lemma lem4606397 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term24 A B s t n) : (term43 A B s t x n) = True.
Proof. exact (@lem4606396 A B x s t n h1). Qed.
Lemma lem4606398 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term24 A B s t n) : (term159 A B s t n) = (term102 A).
Proof. exact (fun_ext (fun x : A => @lem4606397 A B x s t n h1)). Qed.
Lemma lem4606399 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4606400 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term24 A B s t n) : (term24 A B s t n) = (term103 A).
Proof. exact (MK_COMB (@lem4606399 A) (@lem4606398 A B s t n h1)). Qed.
Lemma lem4606402 {A : Type'} (t : Prop) : (term104 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4606403 {A : Type'} (t : Prop) : (term104 A t) = t.
Proof. exact (@lem4606402 A t). Qed.
Lemma lem4606404 {A : Type'} : (term103 A) = True.
Proof. exact (@lem4606403 A True). Qed.
Lemma lem4606405 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term24 A B s t n) : (term24 A B s t n) = True.
Proof. exact (TRANS (@lem4606400 A B s t n h1) (@lem4606404 A)). Qed.
Lemma lem4606406 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (h1 : term24 A B s t n) (h2 : @FINITE A s) : (term160 A B s t n) = (True /\ True).
Proof. exact (MK_COMB (@lem4606390 A s h2) (@lem4606405 A B s t n h1)). Qed.
Lemma lem4606408 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4606409 : (True /\ True) = True.
Proof. exact (@lem4606408 True). Qed.
Lemma lem4606410 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (h1 : term24 A B s t n) (h2 : @FINITE A s) : (term160 A B s t n) = True.
Proof. exact (TRANS (@lem4606406 A B t n s h1 h2) (@lem4606409)). Qed.
Lemma lem4606411 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (h1 : term24 A B s t n) (h2 : @FINITE A s) : True = (term160 A B s t n).
Proof. exact (SYM (@lem4606410 A B t n s h1 h2)). Qed.
Lemma lem4606412 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (h1 : term24 A B s t n) (h2 : @FINITE A s) : term160 A B s t n.
Proof. exact (EQ_MP (@lem4606411 A B t n s h1 h2) (@lem0)). Qed.
Lemma lem4606413 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (h1 : term24 A B s t n) (h2 : @FINITE A s) : term141 A B t s n.
Proof. exact (@lem4606351 A B t s n (@lem4606412 A B t n s h1 h2)). Qed.
Lemma lem4606414 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term24 A B s t n) (h2 : @FINITE A s) (h3 : term25 A s m) : term148 A B t s m n.
Proof. exact (EQ_MP (@lem4606347 A B t n s m h3) (@lem4606413 A B t n s h1 h2)). Qed.
Lemma lem4606415 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term24 A B s t n) (h2 : @FINITE A s) (h3 : term25 A s m) : term161 A B t s m n.
Proof. exact (ex_intro (term162 A B t s m n) (term139 A s n) (@lem4606414 A B t n s m h1 h2 h3)). Qed.
Lemma lem4606416 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term24 A B s t n) (h2 : @FINITE A s) (h3 : term25 A s m) : term111 A B t s m n.
Proof. exact (@lem4606275 A B t s m n (@lem4606415 A B t n s m h1 h2 h3)). Qed.
Lemma lem4606417 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term24 A B s t n) (h2 : @FINITE A s) (h3 : term25 A s m) : term10 A B s t m n.
Proof. exact (EQ_MP (@lem4606244 A B s t m n) (@lem4606416 A B t n s m h1 h2 h3)). Qed.
Lemma lem4606418 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term24 A B s t n) (h2 : @FINITE A s) (h3 : term25 A s m) : term163 A B s t m n.
Proof. exact (conj (@lem4606152 A B t n s h1 h2) (@lem4606417 A B t n s m h1 h2 h3)). Qed.
Lemma lem4606419 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term22 A B t n s m) : term23 A s m.
Proof. exact (proj2 (@lem4605954 A B t n s m h1)). Qed.
Lemma lem4606420 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term22 A B t n s m) : term24 A B s t n.
Proof. exact (proj1 (@lem4605954 A B t n s m h1)). Qed.
Lemma lem4606421 {A : Type'} (s : A -> Prop) (m : nat) (h1 : term23 A s m) : term25 A s m.
Proof. exact (proj2 (@lem4605955 A s m h1)). Qed.
Lemma lem4606422 {A : Type'} (s : A -> Prop) (m : nat) (h1 : term23 A s m) : @FINITE A s.
Proof. exact (proj1 (@lem4605955 A s m h1)). Qed.
Lemma lem4606423 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term24 A B s t n) (h2 : @FINITE A s) (h3 : term25 A s m) : (term25 A s m) = (term163 A B s t m n).
Proof. exact (prop_ext (fun h4 : term25 A s m => @lem4606418 A B t n s m h1 h2 h3) (fun h4 : term163 A B s t m n => @lem4605957 A s m h3)). Qed.
Lemma lem4606424 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term24 A B s t n) (h2 : @FINITE A s) (h3 : term25 A s m) : term163 A B s t m n.
Proof. exact (EQ_MP (@lem4606423 A B t n s m h1 h2 h3) (@lem4605957 A s m h3)). Qed.
Lemma lem4606425 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term24 A B s t n) (h2 : @FINITE A s) (h3 : term25 A s m) : (@FINITE A s) = (term163 A B s t m n).
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem4606424 A B t n s m h1 h2 h3) (fun h4 : term163 A B s t m n => @lem4605958 A s h2)). Qed.
Lemma lem4606426 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term24 A B s t n) (h2 : @FINITE A s) (h3 : term25 A s m) : term163 A B s t m n.
Proof. exact (EQ_MP (@lem4606425 A B t n s m h1 h2 h3) (@lem4605958 A s h2)). Qed.
Lemma lem4606427 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term24 A B s t n) (h2 : @FINITE A s) (h3 : term23 A s m) : (term25 A s m) = (term163 A B s t m n).
Proof. exact (prop_ext (fun h4 : term25 A s m => @lem4606426 A B t n s m h1 h2 h4) (fun h4 : term163 A B s t m n => @lem4606421 A s m h3)). Qed.
Lemma lem4606428 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term24 A B s t n) (h2 : @FINITE A s) (h3 : term23 A s m) : term163 A B s t m n.
Proof. exact (EQ_MP (@lem4606427 A B t n s m h1 h2 h3) (@lem4606421 A s m h3)). Qed.
Lemma lem4606429 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term24 A B s t n) (h2 : term23 A s m) : (@FINITE A s) = (term163 A B s t m n).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem4606428 A B t n s m h1 h3 h2) (fun h3 : term163 A B s t m n => @lem4606422 A s m h2)). Qed.
Lemma lem4606430 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term24 A B s t n) (h2 : term23 A s m) : term163 A B s t m n.
Proof. exact (EQ_MP (@lem4606429 A B t n s m h1 h2) (@lem4606422 A s m h2)). Qed.
Lemma lem4606431 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term24 A B s t n) (h2 : term23 A s m) : (term24 A B s t n) = (term163 A B s t m n).
Proof. exact (prop_ext (fun h3 : term24 A B s t n => @lem4606430 A B t n s m h1 h2) (fun h3 : term163 A B s t m n => @lem4605956 A B s t n h1)). Qed.
Lemma lem4606432 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term24 A B s t n) (h2 : term23 A s m) : term163 A B s t m n.
Proof. exact (EQ_MP (@lem4606431 A B t n s m h1 h2) (@lem4605956 A B s t n h1)). Qed.
Lemma lem4606433 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term24 A B s t n) (h2 : term22 A B t n s m) : (term23 A s m) = (term163 A B s t m n).
Proof. exact (prop_ext (fun h3 : term23 A s m => @lem4606432 A B t n s m h1 h3) (fun h3 : term163 A B s t m n => @lem4606419 A B t n s m h2)). Qed.
Lemma lem4606434 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term24 A B s t n) (h2 : term22 A B t n s m) : term163 A B s t m n.
Proof. exact (EQ_MP (@lem4606433 A B t n s m h1 h2) (@lem4606419 A B t n s m h2)). Qed.
Lemma lem4606435 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term22 A B t n s m) : (term24 A B s t n) = (term163 A B s t m n).
Proof. exact (prop_ext (fun h2 : term24 A B s t n => @lem4606434 A B t n s m h2 h1) (fun h2 : term163 A B s t m n => @lem4606420 A B t n s m h1)). Qed.
Lemma lem4606436 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term22 A B t n s m) : term163 A B s t m n.
Proof. exact (EQ_MP (@lem4606435 A B t n s m h1) (@lem4606420 A B t n s m h1)). Qed.
Lemma lem4606437 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : term164 A B s t m n.
Proof. exact (fun h0 : term22 A B t n s m => @lem4606436 A B t n s m h0). Qed.
Lemma lem4606442 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : term165 A B s t m.
Proof. exact (fun n : nat => @lem4606437 A B s t m n). Qed.
Lemma lem4606447 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : term166 A B s t.
Proof. exact (fun m : nat => @lem4606442 A B s t m). Qed.
Lemma lem4606452 {A B : Type'} (s : A -> Prop) : term167 A B s.
Proof. exact (fun t : type1413 A B => @lem4606447 A B s t). Qed.
Lemma lem4606457 {A B : Type'} : term168 A B.
Proof. exact (fun s : A -> Prop => @lem4606452 A B s). Qed.
