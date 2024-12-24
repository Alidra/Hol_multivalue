Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ADMISSIBLE_COND_term_abbrevs.
Require Import AND_FORALL_THM_spec.
Require Import MONO_FORALL_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import admissible_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm21735_spec.
Require Import thm21736_spec.
Require Import thm21750_spec.
Require Import thm21760_spec.
Require Import thm7_spec.
Lemma lem8133927 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem8133928 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) : term1 A P Q.
Proof. exact (h1). Qed.
Lemma lem8133929 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) (h2 : term0 A P Q) : term2 A P Q.
Proof. exact (@lem8133927 A P Q h2 (@lem8133928 A P Q h1)). Qed.
Lemma lem8133930 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) : term3 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem8133929 A P Q h1 h0). Qed.
Lemma lem8133931 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem8133932 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) (h2 : term0 A P Q) : term2 A P Q.
Proof. exact (@lem8133930 A P Q h1 (@lem8133931 A P Q h2)). Qed.
Lemma lem8133933 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (fun h0 : term1 A P Q => @lem8133932 A P Q h0 h1). Qed.
Lemma lem8133934 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term4 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem8133933 A P Q h0). Qed.
Lemma lem8133936 {A : Type'} (P : A -> Prop) : term5 A P.
Proof. exact (@lem5146 A P). Qed.
Lemma lem8133937 {A : Type'} (P : A -> Prop) : (term5 A P) = (term6 A P).
Proof. exact (eq_refl (term5 A P)). Qed.
Lemma lem8133938 {A : Type'} (P : A -> Prop) : term6 A P.
Proof. exact (EQ_MP (@lem8133937 A P) (@lem8133936 A P)). Qed.
Lemma lem8133939 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term7 A P Q.
Proof. exact (@lem8133938 A P Q). Qed.
Lemma lem8133940 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term7 A P Q) = ((term8 A P Q) = (term9 A P Q)).
Proof. exact (eq_refl (term7 A P Q)). Qed.
Lemma lem8133942 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : term10 _143449 _143452 _143456 _143457 _143462 p.
Proof. exact (@lem8093231 _143449 _143452 _143456 _143457 _143462 p). Qed.
Lemma lem8133943 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : (term10 _143449 _143452 _143456 _143457 _143462 p) = (term11 _143449 _143452 _143456 _143457 _143462 p).
Proof. exact (eq_refl (term10 _143449 _143452 _143456 _143457 _143462 p)). Qed.
Lemma lem8133944 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : term11 _143449 _143452 _143456 _143457 _143462 p.
Proof. exact (EQ_MP (@lem8133943 _143449 _143452 _143456 _143457 _143462 p) (@lem8133942 _143449 _143452 _143456 _143457 _143462 p)). Qed.
Lemma lem8133945 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : term12 _143449 _143452 _143456 _143457 _143462 p lt2.
Proof. exact (@lem8133944 _143449 _143452 _143456 _143457 _143462 p lt2). Qed.
Lemma lem8133946 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : (term12 _143449 _143452 _143456 _143457 _143462 p lt2) = (term13 _143449 _143452 _143456 _143457 _143462 p lt2).
Proof. exact (eq_refl (term12 _143449 _143452 _143456 _143457 _143462 p lt2)). Qed.
Lemma lem8133947 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : term13 _143449 _143452 _143456 _143457 _143462 p lt2.
Proof. exact (EQ_MP (@lem8133946 _143449 _143452 _143456 _143457 _143462 p lt2) (@lem8133945 _143449 _143452 _143456 _143457 _143462 p lt2)). Qed.
Lemma lem8133948 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : term14 _143449 _143452 _143456 _143457 _143462 p lt2 s.
Proof. exact (@lem8133947 _143449 _143452 _143456 _143457 _143462 p lt2 s). Qed.
Lemma lem8133949 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : (term14 _143449 _143452 _143456 _143457 _143462 p lt2 s) = (term15 _143449 _143452 _143456 _143457 _143462 p lt2 s).
Proof. exact (eq_refl (term14 _143449 _143452 _143456 _143457 _143462 p lt2 s)). Qed.
Lemma lem8133950 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : term15 _143449 _143452 _143456 _143457 _143462 p lt2 s.
Proof. exact (EQ_MP (@lem8133949 _143449 _143452 _143456 _143457 _143462 p lt2 s) (@lem8133948 _143449 _143452 _143456 _143457 _143462 p lt2 s)). Qed.
Lemma lem8133951 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : term16 _143449 _143452 _143456 _143457 _143462 p lt2 s t.
Proof. exact (@lem8133950 _143449 _143452 _143456 _143457 _143462 p lt2 s t). Qed.
Lemma lem8133952 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (term16 _143449 _143452 _143456 _143457 _143462 p lt2 s t) = ((@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term17 _143449 _143452 _143456 _143457 _143462 p lt2 s t)).
Proof. exact (eq_refl (term16 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8133959 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term17 _143449 _143452 _143456 _143457 _143462 p lt2 s t).
Proof. exact (EQ_MP (@lem8133952 _143449 _143452 _143456 _143457 _143462 p lt2 s t) (@lem8133951 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8133960 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (t : type560 _144007 _144038 P) : (@admissible _144006 _144038 _144007 Prop P lt2 p s t) = (term18 _144006 _144007 _144038 P p lt2 s t).
Proof. exact (@lem8133959 _144006 _144038 _144007 Prop P p lt2 s t). Qed.
Lemma lem8133961 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (P' : type560 _144007 _144038 P) : (@admissible _144006 _144038 _144007 Prop P lt2 p s P') = (term18 _144006 _144007 _144038 P p lt2 s P').
Proof. exact (@lem8133960 _144006 _144007 _144038 P p lt2 s P'). Qed.
Lemma lem8133990 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8133991 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (P' : type560 _144007 _144038 P) : (term19 _144006 _144007 _144038 P lt2 p s P') = (term20 _144006 _144007 _144038 P p lt2 s P').
Proof. exact (MK_COMB (@lem8133990) (@lem8133961 _144006 _144007 _144038 P p lt2 s P')). Qed.
Lemma lem8133995 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term17 _143449 _143452 _143456 _143457 _143462 p lt2 s t).
Proof. exact (EQ_MP (@lem8133952 _143449 _143452 _143456 _143457 _143462 p lt2 s t) (@lem8133951 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8133996 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (t : type564 _144007 _144038 _144063 P) : (@admissible _144006 _144038 _144007 _144063 P lt2 p s t) = (term21 _144006 _144007 _144038 _144063 P p lt2 s t).
Proof. exact (@lem8133995 _144006 _144038 _144007 _144063 P p lt2 s t). Qed.
Lemma lem8133997 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) : (term22 _144006 _144007 _144038 _144063 P lt2 p P' s h) = (term23 _144006 _144007 _144038 _144063 P p P' lt2 s h).
Proof. exact (@lem8133996 _144006 _144007 _144038 _144063 P (term24 _144007 _144038 P p P') lt2 s h). Qed.
Lemma lem8134015 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8134016 {_144007 _144038 P : Type'} (f : type560 _144007 _144038 P) (y : _144007 -> _144038) : (term26 _144007 _144038 P f y) = (f y).
Proof. exact (@lem8134015 (_144007 -> _144038) (P -> Prop) f y). Qed.
Lemma lem8134017 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) : (term27 _144007 _144038 P p P' f) = (term28 _144007 _144038 P p P' f).
Proof. exact (@lem8134016 _144007 _144038 P (term24 _144007 _144038 P p P') f). Qed.
Lemma lem8134018 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) : (term28 _144007 _144038 P p P' f) = (term29 _144007 _144038 P p P' f).
Proof. exact (eq_refl (term28 _144007 _144038 P p P' f)). Qed.
Lemma lem8134019 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) : (term30 _144007 _144038 P p P') = (term24 _144007 _144038 P p P').
Proof. exact (fun_ext (fun f : _144007 -> _144038 => @lem8134018 _144007 _144038 P p P' f)). Qed.
Lemma lem8134020 {_144007 _144038 : Type'} (f : _144007 -> _144038) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8134021 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) : (term27 _144007 _144038 P p P' f) = (term28 _144007 _144038 P p P' f).
Proof. exact (MK_COMB (@lem8134019 _144007 _144038 P p P') (@lem8134020 _144007 _144038 f)). Qed.
Lemma lem8134022 {P : Type'} : (@eq (P -> Prop)) = (@eq (P -> Prop)).
Proof. exact (eq_refl (@eq (P -> Prop))). Qed.
Lemma lem8134023 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) : (term31 _144007 _144038 P p P' f) = (term32 _144007 _144038 P p P' f).
Proof. exact (MK_COMB (@lem8134022 P) (@lem8134021 _144007 _144038 P p P' f)). Qed.
Lemma lem8134024 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) : (term28 _144007 _144038 P p P' f) = (term29 _144007 _144038 P p P' f).
Proof. exact (eq_refl (term28 _144007 _144038 P p P' f)). Qed.
Lemma lem8134025 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) : ((term27 _144007 _144038 P p P' f) = (term28 _144007 _144038 P p P' f)) = ((term28 _144007 _144038 P p P' f) = (term29 _144007 _144038 P p P' f)).
Proof. exact (MK_COMB (@lem8134023 _144007 _144038 P p P' f) (@lem8134024 _144007 _144038 P p P' f)). Qed.
Lemma lem8134026 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) : (term28 _144007 _144038 P p P' f) = (term29 _144007 _144038 P p P' f).
Proof. exact (EQ_MP (@lem8134025 _144007 _144038 P p P' f) (@lem8134017 _144007 _144038 P p P' f)). Qed.
Lemma lem8134029 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8134030 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term33 _144007 _144038 P p P' f a) = (term34 _144007 _144038 P p P' f a).
Proof. exact (MK_COMB (@lem8134026 _144007 _144038 P p P' f) (@lem8134029 P a)). Qed.
Lemma lem8134032 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8134033 {P : Type'} (f : P -> Prop) (y : P) : (term35 P f y) = (f y).
Proof. exact (@lem8134032 P Prop f y). Qed.
Lemma lem8134034 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term36 _144007 _144038 P p P' f a) = (term34 _144007 _144038 P p P' f a).
Proof. exact (@lem8134033 P (term29 _144007 _144038 P p P' f) a). Qed.
Lemma lem8134035 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (x : P) : (term34 _144007 _144038 P p P' f x) = (term37 _144007 _144038 P p P' f x).
Proof. exact (eq_refl (term34 _144007 _144038 P p P' f x)). Qed.
Lemma lem8134036 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) : (term38 _144007 _144038 P p P' f) = (term29 _144007 _144038 P p P' f).
Proof. exact (fun_ext (fun x : P => @lem8134035 _144007 _144038 P p P' f x)). Qed.
Lemma lem8134037 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8134038 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term36 _144007 _144038 P p P' f a) = (term34 _144007 _144038 P p P' f a).
Proof. exact (MK_COMB (@lem8134036 _144007 _144038 P p P' f) (@lem8134037 P a)). Qed.
Lemma lem8134039 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8134040 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term39 _144007 _144038 P p P' f a) = (term40 _144007 _144038 P p P' f a).
Proof. exact (MK_COMB (@lem8134039) (@lem8134038 _144007 _144038 P p P' f a)). Qed.
Lemma lem8134041 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term34 _144007 _144038 P p P' f a) = (term37 _144007 _144038 P p P' f a).
Proof. exact (eq_refl (term34 _144007 _144038 P p P' f a)). Qed.
Lemma lem8134042 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : ((term36 _144007 _144038 P p P' f a) = (term34 _144007 _144038 P p P' f a)) = ((term34 _144007 _144038 P p P' f a) = (term37 _144007 _144038 P p P' f a)).
Proof. exact (MK_COMB (@lem8134040 _144007 _144038 P p P' f a) (@lem8134041 _144007 _144038 P p P' f a)). Qed.
Lemma lem8134043 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term34 _144007 _144038 P p P' f a) = (term37 _144007 _144038 P p P' f a).
Proof. exact (EQ_MP (@lem8134042 _144007 _144038 P p P' f a) (@lem8134034 _144007 _144038 P p P' f a)). Qed.
Lemma lem8134046 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term33 _144007 _144038 P p P' f a) = (term37 _144007 _144038 P p P' f a).
Proof. exact (TRANS (@lem8134030 _144007 _144038 P p P' f a) (@lem8134043 _144007 _144038 P p P' f a)). Qed.
Lemma lem8134047 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134048 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term41 _144007 _144038 P p P' f a) = (term42 _144007 _144038 P p P' f a).
Proof. exact (MK_COMB (@lem8134047) (@lem8134046 _144007 _144038 P p P' f a)). Qed.
Lemma lem8134052 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8134053 {_144007 _144038 P : Type'} (f : type560 _144007 _144038 P) (y : _144007 -> _144038) : (term26 _144007 _144038 P f y) = (f y).
Proof. exact (@lem8134052 (_144007 -> _144038) (P -> Prop) f y). Qed.
Lemma lem8134054 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) : (term27 _144007 _144038 P p P' g) = (term28 _144007 _144038 P p P' g).
Proof. exact (@lem8134053 _144007 _144038 P (term24 _144007 _144038 P p P') g). Qed.
Lemma lem8134055 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) : (term28 _144007 _144038 P p P' f) = (term29 _144007 _144038 P p P' f).
Proof. exact (eq_refl (term28 _144007 _144038 P p P' f)). Qed.
Lemma lem8134056 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) : (term30 _144007 _144038 P p P') = (term24 _144007 _144038 P p P').
Proof. exact (fun_ext (fun f : _144007 -> _144038 => @lem8134055 _144007 _144038 P p P' f)). Qed.
Lemma lem8134057 {_144007 _144038 : Type'} (g : _144007 -> _144038) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8134058 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) : (term27 _144007 _144038 P p P' g) = (term28 _144007 _144038 P p P' g).
Proof. exact (MK_COMB (@lem8134056 _144007 _144038 P p P') (@lem8134057 _144007 _144038 g)). Qed.
Lemma lem8134059 {P : Type'} : (@eq (P -> Prop)) = (@eq (P -> Prop)).
Proof. exact (eq_refl (@eq (P -> Prop))). Qed.
Lemma lem8134060 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) : (term31 _144007 _144038 P p P' g) = (term32 _144007 _144038 P p P' g).
Proof. exact (MK_COMB (@lem8134059 P) (@lem8134058 _144007 _144038 P p P' g)). Qed.
Lemma lem8134061 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) : (term28 _144007 _144038 P p P' g) = (term29 _144007 _144038 P p P' g).
Proof. exact (eq_refl (term28 _144007 _144038 P p P' g)). Qed.
Lemma lem8134062 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) : ((term27 _144007 _144038 P p P' g) = (term28 _144007 _144038 P p P' g)) = ((term28 _144007 _144038 P p P' g) = (term29 _144007 _144038 P p P' g)).
Proof. exact (MK_COMB (@lem8134060 _144007 _144038 P p P' g) (@lem8134061 _144007 _144038 P p P' g)). Qed.
Lemma lem8134063 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) : (term28 _144007 _144038 P p P' g) = (term29 _144007 _144038 P p P' g).
Proof. exact (EQ_MP (@lem8134062 _144007 _144038 P p P' g) (@lem8134054 _144007 _144038 P p P' g)). Qed.
Lemma lem8134066 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8134067 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term33 _144007 _144038 P p P' g a) = (term34 _144007 _144038 P p P' g a).
Proof. exact (MK_COMB (@lem8134063 _144007 _144038 P p P' g) (@lem8134066 P a)). Qed.
Lemma lem8134069 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8134070 {P : Type'} (f : P -> Prop) (y : P) : (term35 P f y) = (f y).
Proof. exact (@lem8134069 P Prop f y). Qed.
Lemma lem8134071 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term36 _144007 _144038 P p P' g a) = (term34 _144007 _144038 P p P' g a).
Proof. exact (@lem8134070 P (term29 _144007 _144038 P p P' g) a). Qed.
Lemma lem8134072 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (x : P) : (term34 _144007 _144038 P p P' g x) = (term37 _144007 _144038 P p P' g x).
Proof. exact (eq_refl (term34 _144007 _144038 P p P' g x)). Qed.
Lemma lem8134073 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) : (term38 _144007 _144038 P p P' g) = (term29 _144007 _144038 P p P' g).
Proof. exact (fun_ext (fun x : P => @lem8134072 _144007 _144038 P p P' g x)). Qed.
Lemma lem8134074 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8134075 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term36 _144007 _144038 P p P' g a) = (term34 _144007 _144038 P p P' g a).
Proof. exact (MK_COMB (@lem8134073 _144007 _144038 P p P' g) (@lem8134074 P a)). Qed.
Lemma lem8134076 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8134077 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term39 _144007 _144038 P p P' g a) = (term40 _144007 _144038 P p P' g a).
Proof. exact (MK_COMB (@lem8134076) (@lem8134075 _144007 _144038 P p P' g a)). Qed.
Lemma lem8134078 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term34 _144007 _144038 P p P' g a) = (term37 _144007 _144038 P p P' g a).
Proof. exact (eq_refl (term34 _144007 _144038 P p P' g a)). Qed.
Lemma lem8134079 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : ((term36 _144007 _144038 P p P' g a) = (term34 _144007 _144038 P p P' g a)) = ((term34 _144007 _144038 P p P' g a) = (term37 _144007 _144038 P p P' g a)).
Proof. exact (MK_COMB (@lem8134077 _144007 _144038 P p P' g a) (@lem8134078 _144007 _144038 P p P' g a)). Qed.
Lemma lem8134080 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term34 _144007 _144038 P p P' g a) = (term37 _144007 _144038 P p P' g a).
Proof. exact (EQ_MP (@lem8134079 _144007 _144038 P p P' g a) (@lem8134071 _144007 _144038 P p P' g a)). Qed.
Lemma lem8134083 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term33 _144007 _144038 P p P' g a) = (term37 _144007 _144038 P p P' g a).
Proof. exact (TRANS (@lem8134067 _144007 _144038 P p P' g a) (@lem8134080 _144007 _144038 P p P' g a)). Qed.
Lemma lem8134084 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134085 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term41 _144007 _144038 P p P' g a) = (term42 _144007 _144038 P p P' g a).
Proof. exact (MK_COMB (@lem8134084) (@lem8134083 _144007 _144038 P p P' g a)). Qed.
Lemma lem8134094 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) : (term43 _144006 _144007 _144038 P lt2 s a f g) = (term43 _144006 _144007 _144038 P lt2 s a f g).
Proof. exact (eq_refl (term43 _144006 _144007 _144038 P lt2 s a f g)). Qed.
Lemma lem8134095 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) : (term44 _144006 _144007 _144038 P p P' lt2 s a f g) = (term45 _144006 _144007 _144038 P p P' lt2 s a f g).
Proof. exact (MK_COMB (@lem8134085 _144007 _144038 P p P' g a) (@lem8134094 _144006 _144007 _144038 P lt2 s a f g)). Qed.
Lemma lem8134098 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) : (term46 _144006 _144007 _144038 P p P' lt2 s a f g) = (term47 _144006 _144007 _144038 P p P' lt2 s a f g).
Proof. exact (MK_COMB (@lem8134048 _144007 _144038 P p P' f a) (@lem8134095 _144006 _144007 _144038 P p P' lt2 s a f g)). Qed.
Lemma lem8134101 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8134102 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) : (term48 _144006 _144007 _144038 P p P' lt2 s a f g) = (term49 _144006 _144007 _144038 P p P' lt2 s a f g).
Proof. exact (MK_COMB (@lem8134101) (@lem8134098 _144006 _144007 _144038 P p P' lt2 s a f g)). Qed.
Lemma lem8134105 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : ((h f a) = (h g a)) = ((h f a) = (h g a)).
Proof. exact (eq_refl ((h f a) = (h g a))). Qed.
Lemma lem8134106 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term50 _144006 _144007 _144038 _144063 P p P' lt2 s f h g a) = (term51 _144006 _144007 _144038 _144063 P p P' lt2 s f h g a).
Proof. exact (MK_COMB (@lem8134102 _144006 _144007 _144038 P p P' lt2 s a f g) (@lem8134105 _144007 _144038 _144063 P f h g a)). Qed.
Lemma lem8134109 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term52 _144006 _144007 _144038 _144063 P p P' lt2 s f h g) = (term53 _144006 _144007 _144038 _144063 P p P' lt2 s f h g).
Proof. exact (fun_ext (fun a : P => @lem8134106 _144006 _144007 _144038 _144063 P p P' lt2 s f h g a)). Qed.
Lemma lem8134110 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8134111 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term54 _144006 _144007 _144038 _144063 P p P' lt2 s f h g) = (term55 _144006 _144007 _144038 _144063 P p P' lt2 s f h g).
Proof. exact (MK_COMB (@lem8134110 P) (@lem8134109 _144006 _144007 _144038 _144063 P p P' lt2 s f h g)). Qed.
Lemma lem8134116 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) : (term56 _144006 _144007 _144038 _144063 P p P' lt2 s f h) = (term57 _144006 _144007 _144038 _144063 P p P' lt2 s f h).
Proof. exact (fun_ext (fun g : _144007 -> _144038 => @lem8134111 _144006 _144007 _144038 _144063 P p P' lt2 s f h g)). Qed.
Lemma lem8134117 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8134118 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) : (term58 _144006 _144007 _144038 _144063 P p P' lt2 s f h) = (term59 _144006 _144007 _144038 _144063 P p P' lt2 s f h).
Proof. exact (MK_COMB (@lem8134117 _144007 _144038) (@lem8134116 _144006 _144007 _144038 _144063 P p P' lt2 s f h)). Qed.
Lemma lem8134123 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) : (term60 _144006 _144007 _144038 _144063 P p P' lt2 s h) = (term61 _144006 _144007 _144038 _144063 P p P' lt2 s h).
Proof. exact (fun_ext (fun f : _144007 -> _144038 => @lem8134118 _144006 _144007 _144038 _144063 P p P' lt2 s f h)). Qed.
Lemma lem8134124 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8134125 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) : (term23 _144006 _144007 _144038 _144063 P p P' lt2 s h) = (term62 _144006 _144007 _144038 _144063 P p P' lt2 s h).
Proof. exact (MK_COMB (@lem8134124 _144007 _144038) (@lem8134123 _144006 _144007 _144038 _144063 P p P' lt2 s h)). Qed.
Lemma lem8134130 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) : (term22 _144006 _144007 _144038 _144063 P lt2 p P' s h) = (term62 _144006 _144007 _144038 _144063 P p P' lt2 s h).
Proof. exact (TRANS (@lem8133997 _144006 _144007 _144038 _144063 P p P' lt2 s h) (@lem8134125 _144006 _144007 _144038 _144063 P p P' lt2 s h)). Qed.
Lemma lem8134131 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134132 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) : (term63 _144006 _144007 _144038 _144063 P lt2 p P' s h) = (term64 _144006 _144007 _144038 _144063 P p P' lt2 s h).
Proof. exact (MK_COMB (@lem8134131) (@lem8134130 _144006 _144007 _144038 _144063 P p P' lt2 s h)). Qed.
Lemma lem8134134 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term17 _143449 _143452 _143456 _143457 _143462 p lt2 s t).
Proof. exact (EQ_MP (@lem8133952 _143449 _143452 _143456 _143457 _143462 p lt2 s t) (@lem8133951 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8134135 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (t : type564 _144007 _144038 _144063 P) : (@admissible _144006 _144038 _144007 _144063 P lt2 p s t) = (term21 _144006 _144007 _144038 _144063 P p lt2 s t).
Proof. exact (@lem8134134 _144006 _144038 _144007 _144063 P p lt2 s t). Qed.
Lemma lem8134136 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term65 _144006 _144007 _144038 _144063 P lt2 p P' s k) = (term66 _144006 _144007 _144038 _144063 P p P' lt2 s k).
Proof. exact (@lem8134135 _144006 _144007 _144038 _144063 P (term67 _144007 _144038 P p P') lt2 s k). Qed.
Lemma lem8134154 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8134155 {_144007 _144038 P : Type'} (f : type560 _144007 _144038 P) (y : _144007 -> _144038) : (term26 _144007 _144038 P f y) = (f y).
Proof. exact (@lem8134154 (_144007 -> _144038) (P -> Prop) f y). Qed.
Lemma lem8134156 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) : (term68 _144007 _144038 P p P' f) = (term69 _144007 _144038 P p P' f).
Proof. exact (@lem8134155 _144007 _144038 P (term67 _144007 _144038 P p P') f). Qed.
Lemma lem8134157 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) : (term69 _144007 _144038 P p P' f) = (term70 _144007 _144038 P p P' f).
Proof. exact (eq_refl (term69 _144007 _144038 P p P' f)). Qed.
Lemma lem8134158 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) : (term71 _144007 _144038 P p P') = (term67 _144007 _144038 P p P').
Proof. exact (fun_ext (fun f : _144007 -> _144038 => @lem8134157 _144007 _144038 P p P' f)). Qed.
Lemma lem8134159 {_144007 _144038 : Type'} (f : _144007 -> _144038) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8134160 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) : (term68 _144007 _144038 P p P' f) = (term69 _144007 _144038 P p P' f).
Proof. exact (MK_COMB (@lem8134158 _144007 _144038 P p P') (@lem8134159 _144007 _144038 f)). Qed.
Lemma lem8134161 {P : Type'} : (@eq (P -> Prop)) = (@eq (P -> Prop)).
Proof. exact (eq_refl (@eq (P -> Prop))). Qed.
Lemma lem8134162 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) : (term72 _144007 _144038 P p P' f) = (term73 _144007 _144038 P p P' f).
Proof. exact (MK_COMB (@lem8134161 P) (@lem8134160 _144007 _144038 P p P' f)). Qed.
Lemma lem8134163 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) : (term69 _144007 _144038 P p P' f) = (term70 _144007 _144038 P p P' f).
Proof. exact (eq_refl (term69 _144007 _144038 P p P' f)). Qed.
Lemma lem8134164 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) : ((term68 _144007 _144038 P p P' f) = (term69 _144007 _144038 P p P' f)) = ((term69 _144007 _144038 P p P' f) = (term70 _144007 _144038 P p P' f)).
Proof. exact (MK_COMB (@lem8134162 _144007 _144038 P p P' f) (@lem8134163 _144007 _144038 P p P' f)). Qed.
Lemma lem8134165 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) : (term69 _144007 _144038 P p P' f) = (term70 _144007 _144038 P p P' f).
Proof. exact (EQ_MP (@lem8134164 _144007 _144038 P p P' f) (@lem8134156 _144007 _144038 P p P' f)). Qed.
Lemma lem8134168 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8134169 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term74 _144007 _144038 P p P' f a) = (term75 _144007 _144038 P p P' f a).
Proof. exact (MK_COMB (@lem8134165 _144007 _144038 P p P' f) (@lem8134168 P a)). Qed.
Lemma lem8134171 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8134172 {P : Type'} (f : P -> Prop) (y : P) : (term35 P f y) = (f y).
Proof. exact (@lem8134171 P Prop f y). Qed.
Lemma lem8134173 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term76 _144007 _144038 P p P' f a) = (term75 _144007 _144038 P p P' f a).
Proof. exact (@lem8134172 P (term70 _144007 _144038 P p P' f) a). Qed.
Lemma lem8134174 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (x : P) : (term75 _144007 _144038 P p P' f x) = (term77 _144007 _144038 P p P' f x).
Proof. exact (eq_refl (term75 _144007 _144038 P p P' f x)). Qed.
Lemma lem8134175 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) : (term78 _144007 _144038 P p P' f) = (term70 _144007 _144038 P p P' f).
Proof. exact (fun_ext (fun x : P => @lem8134174 _144007 _144038 P p P' f x)). Qed.
Lemma lem8134176 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8134177 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term76 _144007 _144038 P p P' f a) = (term75 _144007 _144038 P p P' f a).
Proof. exact (MK_COMB (@lem8134175 _144007 _144038 P p P' f) (@lem8134176 P a)). Qed.
Lemma lem8134178 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8134179 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term79 _144007 _144038 P p P' f a) = (term80 _144007 _144038 P p P' f a).
Proof. exact (MK_COMB (@lem8134178) (@lem8134177 _144007 _144038 P p P' f a)). Qed.
Lemma lem8134180 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term75 _144007 _144038 P p P' f a) = (term77 _144007 _144038 P p P' f a).
Proof. exact (eq_refl (term75 _144007 _144038 P p P' f a)). Qed.
Lemma lem8134181 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : ((term76 _144007 _144038 P p P' f a) = (term75 _144007 _144038 P p P' f a)) = ((term75 _144007 _144038 P p P' f a) = (term77 _144007 _144038 P p P' f a)).
Proof. exact (MK_COMB (@lem8134179 _144007 _144038 P p P' f a) (@lem8134180 _144007 _144038 P p P' f a)). Qed.
Lemma lem8134182 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term75 _144007 _144038 P p P' f a) = (term77 _144007 _144038 P p P' f a).
Proof. exact (EQ_MP (@lem8134181 _144007 _144038 P p P' f a) (@lem8134173 _144007 _144038 P p P' f a)). Qed.
Lemma lem8134185 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term74 _144007 _144038 P p P' f a) = (term77 _144007 _144038 P p P' f a).
Proof. exact (TRANS (@lem8134169 _144007 _144038 P p P' f a) (@lem8134182 _144007 _144038 P p P' f a)). Qed.
Lemma lem8134186 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134187 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term81 _144007 _144038 P p P' f a) = (term82 _144007 _144038 P p P' f a).
Proof. exact (MK_COMB (@lem8134186) (@lem8134185 _144007 _144038 P p P' f a)). Qed.
Lemma lem8134191 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8134192 {_144007 _144038 P : Type'} (f : type560 _144007 _144038 P) (y : _144007 -> _144038) : (term26 _144007 _144038 P f y) = (f y).
Proof. exact (@lem8134191 (_144007 -> _144038) (P -> Prop) f y). Qed.
Lemma lem8134193 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) : (term68 _144007 _144038 P p P' g) = (term69 _144007 _144038 P p P' g).
Proof. exact (@lem8134192 _144007 _144038 P (term67 _144007 _144038 P p P') g). Qed.
Lemma lem8134194 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) : (term69 _144007 _144038 P p P' f) = (term70 _144007 _144038 P p P' f).
Proof. exact (eq_refl (term69 _144007 _144038 P p P' f)). Qed.
Lemma lem8134195 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) : (term71 _144007 _144038 P p P') = (term67 _144007 _144038 P p P').
Proof. exact (fun_ext (fun f : _144007 -> _144038 => @lem8134194 _144007 _144038 P p P' f)). Qed.
Lemma lem8134196 {_144007 _144038 : Type'} (g : _144007 -> _144038) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8134197 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) : (term68 _144007 _144038 P p P' g) = (term69 _144007 _144038 P p P' g).
Proof. exact (MK_COMB (@lem8134195 _144007 _144038 P p P') (@lem8134196 _144007 _144038 g)). Qed.
Lemma lem8134198 {P : Type'} : (@eq (P -> Prop)) = (@eq (P -> Prop)).
Proof. exact (eq_refl (@eq (P -> Prop))). Qed.
Lemma lem8134199 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) : (term72 _144007 _144038 P p P' g) = (term73 _144007 _144038 P p P' g).
Proof. exact (MK_COMB (@lem8134198 P) (@lem8134197 _144007 _144038 P p P' g)). Qed.
Lemma lem8134200 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) : (term69 _144007 _144038 P p P' g) = (term70 _144007 _144038 P p P' g).
Proof. exact (eq_refl (term69 _144007 _144038 P p P' g)). Qed.
Lemma lem8134201 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) : ((term68 _144007 _144038 P p P' g) = (term69 _144007 _144038 P p P' g)) = ((term69 _144007 _144038 P p P' g) = (term70 _144007 _144038 P p P' g)).
Proof. exact (MK_COMB (@lem8134199 _144007 _144038 P p P' g) (@lem8134200 _144007 _144038 P p P' g)). Qed.
Lemma lem8134202 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) : (term69 _144007 _144038 P p P' g) = (term70 _144007 _144038 P p P' g).
Proof. exact (EQ_MP (@lem8134201 _144007 _144038 P p P' g) (@lem8134193 _144007 _144038 P p P' g)). Qed.
Lemma lem8134205 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8134206 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term74 _144007 _144038 P p P' g a) = (term75 _144007 _144038 P p P' g a).
Proof. exact (MK_COMB (@lem8134202 _144007 _144038 P p P' g) (@lem8134205 P a)). Qed.
Lemma lem8134208 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8134209 {P : Type'} (f : P -> Prop) (y : P) : (term35 P f y) = (f y).
Proof. exact (@lem8134208 P Prop f y). Qed.
Lemma lem8134210 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term76 _144007 _144038 P p P' g a) = (term75 _144007 _144038 P p P' g a).
Proof. exact (@lem8134209 P (term70 _144007 _144038 P p P' g) a). Qed.
Lemma lem8134211 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (x : P) : (term75 _144007 _144038 P p P' g x) = (term77 _144007 _144038 P p P' g x).
Proof. exact (eq_refl (term75 _144007 _144038 P p P' g x)). Qed.
Lemma lem8134212 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) : (term78 _144007 _144038 P p P' g) = (term70 _144007 _144038 P p P' g).
Proof. exact (fun_ext (fun x : P => @lem8134211 _144007 _144038 P p P' g x)). Qed.
Lemma lem8134213 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8134214 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term76 _144007 _144038 P p P' g a) = (term75 _144007 _144038 P p P' g a).
Proof. exact (MK_COMB (@lem8134212 _144007 _144038 P p P' g) (@lem8134213 P a)). Qed.
Lemma lem8134215 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8134216 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term79 _144007 _144038 P p P' g a) = (term80 _144007 _144038 P p P' g a).
Proof. exact (MK_COMB (@lem8134215) (@lem8134214 _144007 _144038 P p P' g a)). Qed.
Lemma lem8134217 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term75 _144007 _144038 P p P' g a) = (term77 _144007 _144038 P p P' g a).
Proof. exact (eq_refl (term75 _144007 _144038 P p P' g a)). Qed.
Lemma lem8134218 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : ((term76 _144007 _144038 P p P' g a) = (term75 _144007 _144038 P p P' g a)) = ((term75 _144007 _144038 P p P' g a) = (term77 _144007 _144038 P p P' g a)).
Proof. exact (MK_COMB (@lem8134216 _144007 _144038 P p P' g a) (@lem8134217 _144007 _144038 P p P' g a)). Qed.
Lemma lem8134219 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term75 _144007 _144038 P p P' g a) = (term77 _144007 _144038 P p P' g a).
Proof. exact (EQ_MP (@lem8134218 _144007 _144038 P p P' g a) (@lem8134210 _144007 _144038 P p P' g a)). Qed.
Lemma lem8134222 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term74 _144007 _144038 P p P' g a) = (term77 _144007 _144038 P p P' g a).
Proof. exact (TRANS (@lem8134206 _144007 _144038 P p P' g a) (@lem8134219 _144007 _144038 P p P' g a)). Qed.
Lemma lem8134223 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134224 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term81 _144007 _144038 P p P' g a) = (term82 _144007 _144038 P p P' g a).
Proof. exact (MK_COMB (@lem8134223) (@lem8134222 _144007 _144038 P p P' g a)). Qed.
Lemma lem8134233 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) : (term43 _144006 _144007 _144038 P lt2 s a f g) = (term43 _144006 _144007 _144038 P lt2 s a f g).
Proof. exact (eq_refl (term43 _144006 _144007 _144038 P lt2 s a f g)). Qed.
Lemma lem8134234 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) : (term83 _144006 _144007 _144038 P p P' lt2 s a f g) = (term84 _144006 _144007 _144038 P p P' lt2 s a f g).
Proof. exact (MK_COMB (@lem8134224 _144007 _144038 P p P' g a) (@lem8134233 _144006 _144007 _144038 P lt2 s a f g)). Qed.
Lemma lem8134237 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) : (term85 _144006 _144007 _144038 P p P' lt2 s a f g) = (term86 _144006 _144007 _144038 P p P' lt2 s a f g).
Proof. exact (MK_COMB (@lem8134187 _144007 _144038 P p P' f a) (@lem8134234 _144006 _144007 _144038 P p P' lt2 s a f g)). Qed.
Lemma lem8134240 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8134241 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) : (term87 _144006 _144007 _144038 P p P' lt2 s a f g) = (term88 _144006 _144007 _144038 P p P' lt2 s a f g).
Proof. exact (MK_COMB (@lem8134240) (@lem8134237 _144006 _144007 _144038 P p P' lt2 s a f g)). Qed.
Lemma lem8134244 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : ((k f a) = (k g a)) = ((k f a) = (k g a)).
Proof. exact (eq_refl ((k f a) = (k g a))). Qed.
Lemma lem8134245 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term89 _144006 _144007 _144038 _144063 P p P' lt2 s f k g a) = (term90 _144006 _144007 _144038 _144063 P p P' lt2 s f k g a).
Proof. exact (MK_COMB (@lem8134241 _144006 _144007 _144038 P p P' lt2 s a f g) (@lem8134244 _144007 _144038 _144063 P f k g a)). Qed.
Lemma lem8134248 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term91 _144006 _144007 _144038 _144063 P p P' lt2 s f k g) = (term92 _144006 _144007 _144038 _144063 P p P' lt2 s f k g).
Proof. exact (fun_ext (fun a : P => @lem8134245 _144006 _144007 _144038 _144063 P p P' lt2 s f k g a)). Qed.
Lemma lem8134249 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8134250 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term93 _144006 _144007 _144038 _144063 P p P' lt2 s f k g) = (term94 _144006 _144007 _144038 _144063 P p P' lt2 s f k g).
Proof. exact (MK_COMB (@lem8134249 P) (@lem8134248 _144006 _144007 _144038 _144063 P p P' lt2 s f k g)). Qed.
Lemma lem8134255 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term95 _144006 _144007 _144038 _144063 P p P' lt2 s f k) = (term96 _144006 _144007 _144038 _144063 P p P' lt2 s f k).
Proof. exact (fun_ext (fun g : _144007 -> _144038 => @lem8134250 _144006 _144007 _144038 _144063 P p P' lt2 s f k g)). Qed.
Lemma lem8134256 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8134257 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term97 _144006 _144007 _144038 _144063 P p P' lt2 s f k) = (term98 _144006 _144007 _144038 _144063 P p P' lt2 s f k).
Proof. exact (MK_COMB (@lem8134256 _144007 _144038) (@lem8134255 _144006 _144007 _144038 _144063 P p P' lt2 s f k)). Qed.
Lemma lem8134262 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term99 _144006 _144007 _144038 _144063 P p P' lt2 s k) = (term100 _144006 _144007 _144038 _144063 P p P' lt2 s k).
Proof. exact (fun_ext (fun f : _144007 -> _144038 => @lem8134257 _144006 _144007 _144038 _144063 P p P' lt2 s f k)). Qed.
Lemma lem8134263 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8134264 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term66 _144006 _144007 _144038 _144063 P p P' lt2 s k) = (term101 _144006 _144007 _144038 _144063 P p P' lt2 s k).
Proof. exact (MK_COMB (@lem8134263 _144007 _144038) (@lem8134262 _144006 _144007 _144038 _144063 P p P' lt2 s k)). Qed.
Lemma lem8134269 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term65 _144006 _144007 _144038 _144063 P lt2 p P' s k) = (term101 _144006 _144007 _144038 _144063 P p P' lt2 s k).
Proof. exact (TRANS (@lem8134136 _144006 _144007 _144038 _144063 P p P' lt2 s k) (@lem8134264 _144006 _144007 _144038 _144063 P p P' lt2 s k)). Qed.
Lemma lem8134270 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term102 _144006 _144007 _144038 _144063 P h lt2 p P' s k) = (term103 _144006 _144007 _144038 _144063 P h p P' lt2 s k).
Proof. exact (MK_COMB (@lem8134132 _144006 _144007 _144038 _144063 P p P' lt2 s h) (@lem8134269 _144006 _144007 _144038 _144063 P p P' lt2 s k)). Qed.
Lemma lem8134272 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term8 A P Q) = (term9 A P Q).
Proof. exact (EQ_MP (@lem8133940 A P Q) (@lem8133939 A P Q)). Qed.
Lemma lem8134273 {_144007 _144038 : Type'} (P : type572 _144007 _144038) (Q : type572 _144007 _144038) : (term104 _144007 _144038 P Q) = (term105 _144007 _144038 P Q).
Proof. exact (@lem8134272 (_144007 -> _144038) P Q). Qed.
Lemma lem8134274 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term106 _144006 _144007 _144038 _144063 P h p P' lt2 s k) = (term107 _144006 _144007 _144038 _144063 P h p P' lt2 s k).
Proof. exact (@lem8134273 _144007 _144038 (term61 _144006 _144007 _144038 _144063 P p P' lt2 s h) (term100 _144006 _144007 _144038 _144063 P p P' lt2 s k)). Qed.
Lemma lem8134275 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) : (term108 _144006 _144007 _144038 _144063 P p P' lt2 s h f) = (term59 _144006 _144007 _144038 _144063 P p P' lt2 s f h).
Proof. exact (eq_refl (term108 _144006 _144007 _144038 _144063 P p P' lt2 s h f)). Qed.
Lemma lem8134276 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) : (term109 _144006 _144007 _144038 _144063 P p P' lt2 s h) = (term61 _144006 _144007 _144038 _144063 P p P' lt2 s h).
Proof. exact (fun_ext (fun f : _144007 -> _144038 => @lem8134275 _144006 _144007 _144038 _144063 P p P' lt2 s f h)). Qed.
Lemma lem8134277 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8134278 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) : (term110 _144006 _144007 _144038 _144063 P p P' lt2 s h) = (term62 _144006 _144007 _144038 _144063 P p P' lt2 s h).
Proof. exact (MK_COMB (@lem8134277 _144007 _144038) (@lem8134276 _144006 _144007 _144038 _144063 P p P' lt2 s h)). Qed.
Lemma lem8134279 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134280 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) : (term111 _144006 _144007 _144038 _144063 P p P' lt2 s h) = (term64 _144006 _144007 _144038 _144063 P p P' lt2 s h).
Proof. exact (MK_COMB (@lem8134279) (@lem8134278 _144006 _144007 _144038 _144063 P p P' lt2 s h)). Qed.
Lemma lem8134281 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term112 _144006 _144007 _144038 _144063 P p P' lt2 s k f) = (term98 _144006 _144007 _144038 _144063 P p P' lt2 s f k).
Proof. exact (eq_refl (term112 _144006 _144007 _144038 _144063 P p P' lt2 s k f)). Qed.
Lemma lem8134282 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term113 _144006 _144007 _144038 _144063 P p P' lt2 s k) = (term100 _144006 _144007 _144038 _144063 P p P' lt2 s k).
Proof. exact (fun_ext (fun f : _144007 -> _144038 => @lem8134281 _144006 _144007 _144038 _144063 P p P' lt2 s f k)). Qed.
Lemma lem8134283 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8134284 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term114 _144006 _144007 _144038 _144063 P p P' lt2 s k) = (term101 _144006 _144007 _144038 _144063 P p P' lt2 s k).
Proof. exact (MK_COMB (@lem8134283 _144007 _144038) (@lem8134282 _144006 _144007 _144038 _144063 P p P' lt2 s k)). Qed.
Lemma lem8134285 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term106 _144006 _144007 _144038 _144063 P h p P' lt2 s k) = (term103 _144006 _144007 _144038 _144063 P h p P' lt2 s k).
Proof. exact (MK_COMB (@lem8134280 _144006 _144007 _144038 _144063 P p P' lt2 s h) (@lem8134284 _144006 _144007 _144038 _144063 P p P' lt2 s k)). Qed.
Lemma lem8134286 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8134287 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term115 _144006 _144007 _144038 _144063 P h p P' lt2 s k) = (term116 _144006 _144007 _144038 _144063 P h p P' lt2 s k).
Proof. exact (MK_COMB (@lem8134286) (@lem8134285 _144006 _144007 _144038 _144063 P h p P' lt2 s k)). Qed.
Lemma lem8134288 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) : (term108 _144006 _144007 _144038 _144063 P p P' lt2 s h f) = (term59 _144006 _144007 _144038 _144063 P p P' lt2 s f h).
Proof. exact (eq_refl (term108 _144006 _144007 _144038 _144063 P p P' lt2 s h f)). Qed.
Lemma lem8134289 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134290 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) : (term117 _144006 _144007 _144038 _144063 P p P' lt2 s h f) = (term118 _144006 _144007 _144038 _144063 P p P' lt2 s f h).
Proof. exact (MK_COMB (@lem8134289) (@lem8134288 _144006 _144007 _144038 _144063 P p P' lt2 s f h)). Qed.
Lemma lem8134291 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term112 _144006 _144007 _144038 _144063 P p P' lt2 s k f) = (term98 _144006 _144007 _144038 _144063 P p P' lt2 s f k).
Proof. exact (eq_refl (term112 _144006 _144007 _144038 _144063 P p P' lt2 s k f)). Qed.
Lemma lem8134292 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term119 _144006 _144007 _144038 _144063 P h p P' lt2 s k f) = (term120 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (MK_COMB (@lem8134290 _144006 _144007 _144038 _144063 P p P' lt2 s f h) (@lem8134291 _144006 _144007 _144038 _144063 P p P' lt2 s f k)). Qed.
Lemma lem8134293 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term121 _144006 _144007 _144038 _144063 P h p P' lt2 s k) = (term122 _144006 _144007 _144038 _144063 P h p P' lt2 s k).
Proof. exact (fun_ext (fun f : _144007 -> _144038 => @lem8134292 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)). Qed.
Lemma lem8134294 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8134295 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term107 _144006 _144007 _144038 _144063 P h p P' lt2 s k) = (term123 _144006 _144007 _144038 _144063 P h p P' lt2 s k).
Proof. exact (MK_COMB (@lem8134294 _144007 _144038) (@lem8134293 _144006 _144007 _144038 _144063 P h p P' lt2 s k)). Qed.
Lemma lem8134296 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : ((term106 _144006 _144007 _144038 _144063 P h p P' lt2 s k) = (term107 _144006 _144007 _144038 _144063 P h p P' lt2 s k)) = ((term103 _144006 _144007 _144038 _144063 P h p P' lt2 s k) = (term123 _144006 _144007 _144038 _144063 P h p P' lt2 s k)).
Proof. exact (MK_COMB (@lem8134287 _144006 _144007 _144038 _144063 P h p P' lt2 s k) (@lem8134295 _144006 _144007 _144038 _144063 P h p P' lt2 s k)). Qed.
Lemma lem8134297 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term103 _144006 _144007 _144038 _144063 P h p P' lt2 s k) = (term123 _144006 _144007 _144038 _144063 P h p P' lt2 s k).
Proof. exact (EQ_MP (@lem8134296 _144006 _144007 _144038 _144063 P h p P' lt2 s k) (@lem8134274 _144006 _144007 _144038 _144063 P h p P' lt2 s k)). Qed.
Lemma lem8134303 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term8 A P Q) = (term9 A P Q).
Proof. exact (EQ_MP (@lem8133940 A P Q) (@lem8133939 A P Q)). Qed.
Lemma lem8134304 {_144007 _144038 : Type'} (P : type572 _144007 _144038) (Q : type572 _144007 _144038) : (term104 _144007 _144038 P Q) = (term105 _144007 _144038 P Q).
Proof. exact (@lem8134303 (_144007 -> _144038) P Q). Qed.
Lemma lem8134305 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term124 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) = (term125 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (@lem8134304 _144007 _144038 (term57 _144006 _144007 _144038 _144063 P p P' lt2 s f h) (term96 _144006 _144007 _144038 _144063 P p P' lt2 s f k)). Qed.
Lemma lem8134306 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term126 _144006 _144007 _144038 _144063 P p P' lt2 s f h g) = (term55 _144006 _144007 _144038 _144063 P p P' lt2 s f h g).
Proof. exact (eq_refl (term126 _144006 _144007 _144038 _144063 P p P' lt2 s f h g)). Qed.
Lemma lem8134307 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) : (term127 _144006 _144007 _144038 _144063 P p P' lt2 s f h) = (term57 _144006 _144007 _144038 _144063 P p P' lt2 s f h).
Proof. exact (fun_ext (fun g : _144007 -> _144038 => @lem8134306 _144006 _144007 _144038 _144063 P p P' lt2 s f h g)). Qed.
Lemma lem8134308 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8134309 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) : (term128 _144006 _144007 _144038 _144063 P p P' lt2 s f h) = (term59 _144006 _144007 _144038 _144063 P p P' lt2 s f h).
Proof. exact (MK_COMB (@lem8134308 _144007 _144038) (@lem8134307 _144006 _144007 _144038 _144063 P p P' lt2 s f h)). Qed.
Lemma lem8134310 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134311 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) : (term129 _144006 _144007 _144038 _144063 P p P' lt2 s f h) = (term118 _144006 _144007 _144038 _144063 P p P' lt2 s f h).
Proof. exact (MK_COMB (@lem8134310) (@lem8134309 _144006 _144007 _144038 _144063 P p P' lt2 s f h)). Qed.
Lemma lem8134312 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term130 _144006 _144007 _144038 _144063 P p P' lt2 s f k g) = (term94 _144006 _144007 _144038 _144063 P p P' lt2 s f k g).
Proof. exact (eq_refl (term130 _144006 _144007 _144038 _144063 P p P' lt2 s f k g)). Qed.
Lemma lem8134313 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term131 _144006 _144007 _144038 _144063 P p P' lt2 s f k) = (term96 _144006 _144007 _144038 _144063 P p P' lt2 s f k).
Proof. exact (fun_ext (fun g : _144007 -> _144038 => @lem8134312 _144006 _144007 _144038 _144063 P p P' lt2 s f k g)). Qed.
Lemma lem8134314 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8134315 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term132 _144006 _144007 _144038 _144063 P p P' lt2 s f k) = (term98 _144006 _144007 _144038 _144063 P p P' lt2 s f k).
Proof. exact (MK_COMB (@lem8134314 _144007 _144038) (@lem8134313 _144006 _144007 _144038 _144063 P p P' lt2 s f k)). Qed.
Lemma lem8134316 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term124 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) = (term120 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (MK_COMB (@lem8134311 _144006 _144007 _144038 _144063 P p P' lt2 s f h) (@lem8134315 _144006 _144007 _144038 _144063 P p P' lt2 s f k)). Qed.
Lemma lem8134317 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8134318 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term133 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) = (term134 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (MK_COMB (@lem8134317) (@lem8134316 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)). Qed.
Lemma lem8134319 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term126 _144006 _144007 _144038 _144063 P p P' lt2 s f h g) = (term55 _144006 _144007 _144038 _144063 P p P' lt2 s f h g).
Proof. exact (eq_refl (term126 _144006 _144007 _144038 _144063 P p P' lt2 s f h g)). Qed.
Lemma lem8134320 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134321 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term135 _144006 _144007 _144038 _144063 P p P' lt2 s f h g) = (term136 _144006 _144007 _144038 _144063 P p P' lt2 s f h g).
Proof. exact (MK_COMB (@lem8134320) (@lem8134319 _144006 _144007 _144038 _144063 P p P' lt2 s f h g)). Qed.
Lemma lem8134322 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term130 _144006 _144007 _144038 _144063 P p P' lt2 s f k g) = (term94 _144006 _144007 _144038 _144063 P p P' lt2 s f k g).
Proof. exact (eq_refl (term130 _144006 _144007 _144038 _144063 P p P' lt2 s f k g)). Qed.
Lemma lem8134323 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term137 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) = (term138 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g).
Proof. exact (MK_COMB (@lem8134321 _144006 _144007 _144038 _144063 P p P' lt2 s f h g) (@lem8134322 _144006 _144007 _144038 _144063 P p P' lt2 s f k g)). Qed.
Lemma lem8134324 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term139 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) = (term140 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (fun_ext (fun g : _144007 -> _144038 => @lem8134323 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)). Qed.
Lemma lem8134325 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8134326 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term125 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) = (term141 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (MK_COMB (@lem8134325 _144007 _144038) (@lem8134324 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)). Qed.
Lemma lem8134327 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : ((term124 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) = (term125 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)) = ((term120 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) = (term141 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)).
Proof. exact (MK_COMB (@lem8134318 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) (@lem8134326 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)). Qed.
Lemma lem8134328 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term120 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) = (term141 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (EQ_MP (@lem8134327 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) (@lem8134305 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)). Qed.
Lemma lem8134334 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term8 A P Q) = (term9 A P Q).
Proof. exact (EQ_MP (@lem8133940 A P Q) (@lem8133939 A P Q)). Qed.
Lemma lem8134335 {P : Type'} (P' : P -> Prop) (Q : P -> Prop) : (term8 P P' Q) = (term9 P P' Q).
Proof. exact (@lem8134334 P P' Q). Qed.
Lemma lem8134336 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term142 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) = (term143 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g).
Proof. exact (@lem8134335 P (term53 _144006 _144007 _144038 _144063 P p P' lt2 s f h g) (term92 _144006 _144007 _144038 _144063 P p P' lt2 s f k g)). Qed.
Lemma lem8134337 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term144 _144006 _144007 _144038 _144063 P p P' lt2 s f h g a) = (term51 _144006 _144007 _144038 _144063 P p P' lt2 s f h g a).
Proof. exact (eq_refl (term144 _144006 _144007 _144038 _144063 P p P' lt2 s f h g a)). Qed.
Lemma lem8134338 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term145 _144006 _144007 _144038 _144063 P p P' lt2 s f h g) = (term53 _144006 _144007 _144038 _144063 P p P' lt2 s f h g).
Proof. exact (fun_ext (fun a : P => @lem8134337 _144006 _144007 _144038 _144063 P p P' lt2 s f h g a)). Qed.
Lemma lem8134339 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8134340 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term146 _144006 _144007 _144038 _144063 P p P' lt2 s f h g) = (term55 _144006 _144007 _144038 _144063 P p P' lt2 s f h g).
Proof. exact (MK_COMB (@lem8134339 P) (@lem8134338 _144006 _144007 _144038 _144063 P p P' lt2 s f h g)). Qed.
Lemma lem8134341 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134342 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term147 _144006 _144007 _144038 _144063 P p P' lt2 s f h g) = (term136 _144006 _144007 _144038 _144063 P p P' lt2 s f h g).
Proof. exact (MK_COMB (@lem8134341) (@lem8134340 _144006 _144007 _144038 _144063 P p P' lt2 s f h g)). Qed.
Lemma lem8134343 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term148 _144006 _144007 _144038 _144063 P p P' lt2 s f k g a) = (term90 _144006 _144007 _144038 _144063 P p P' lt2 s f k g a).
Proof. exact (eq_refl (term148 _144006 _144007 _144038 _144063 P p P' lt2 s f k g a)). Qed.
Lemma lem8134344 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term149 _144006 _144007 _144038 _144063 P p P' lt2 s f k g) = (term92 _144006 _144007 _144038 _144063 P p P' lt2 s f k g).
Proof. exact (fun_ext (fun a : P => @lem8134343 _144006 _144007 _144038 _144063 P p P' lt2 s f k g a)). Qed.
Lemma lem8134345 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8134346 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term150 _144006 _144007 _144038 _144063 P p P' lt2 s f k g) = (term94 _144006 _144007 _144038 _144063 P p P' lt2 s f k g).
Proof. exact (MK_COMB (@lem8134345 P) (@lem8134344 _144006 _144007 _144038 _144063 P p P' lt2 s f k g)). Qed.
Lemma lem8134347 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term142 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) = (term138 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g).
Proof. exact (MK_COMB (@lem8134342 _144006 _144007 _144038 _144063 P p P' lt2 s f h g) (@lem8134346 _144006 _144007 _144038 _144063 P p P' lt2 s f k g)). Qed.
Lemma lem8134348 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8134349 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term151 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) = (term152 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g).
Proof. exact (MK_COMB (@lem8134348) (@lem8134347 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)). Qed.
Lemma lem8134350 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term144 _144006 _144007 _144038 _144063 P p P' lt2 s f h g a) = (term51 _144006 _144007 _144038 _144063 P p P' lt2 s f h g a).
Proof. exact (eq_refl (term144 _144006 _144007 _144038 _144063 P p P' lt2 s f h g a)). Qed.
Lemma lem8134351 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134352 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term153 _144006 _144007 _144038 _144063 P p P' lt2 s f h g a) = (term154 _144006 _144007 _144038 _144063 P p P' lt2 s f h g a).
Proof. exact (MK_COMB (@lem8134351) (@lem8134350 _144006 _144007 _144038 _144063 P p P' lt2 s f h g a)). Qed.
Lemma lem8134353 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term148 _144006 _144007 _144038 _144063 P p P' lt2 s f k g a) = (term90 _144006 _144007 _144038 _144063 P p P' lt2 s f k g a).
Proof. exact (eq_refl (term148 _144006 _144007 _144038 _144063 P p P' lt2 s f k g a)). Qed.
Lemma lem8134354 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term155 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a) = (term156 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a).
Proof. exact (MK_COMB (@lem8134352 _144006 _144007 _144038 _144063 P p P' lt2 s f h g a) (@lem8134353 _144006 _144007 _144038 _144063 P p P' lt2 s f k g a)). Qed.
Lemma lem8134355 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term157 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) = (term158 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g).
Proof. exact (fun_ext (fun a : P => @lem8134354 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a)). Qed.
Lemma lem8134356 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8134357 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term143 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) = (term159 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g).
Proof. exact (MK_COMB (@lem8134356 P) (@lem8134355 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)). Qed.
Lemma lem8134358 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : ((term142 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) = (term143 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)) = ((term138 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) = (term159 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)).
Proof. exact (MK_COMB (@lem8134349 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) (@lem8134357 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)). Qed.
Lemma lem8134359 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term138 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) = (term159 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g).
Proof. exact (EQ_MP (@lem8134358 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) (@lem8134336 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)). Qed.
Lemma lem8134406 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term140 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) = (term160 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (fun_ext (fun g : _144007 -> _144038 => @lem8134359 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)). Qed.
Lemma lem8134407 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8134408 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term141 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) = (term161 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (MK_COMB (@lem8134407 _144007 _144038) (@lem8134406 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)). Qed.
Lemma lem8134413 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term120 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) = (term161 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (TRANS (@lem8134328 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) (@lem8134408 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)). Qed.
Lemma lem8134414 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term122 _144006 _144007 _144038 _144063 P h p P' lt2 s k) = (term162 _144006 _144007 _144038 _144063 P h p P' lt2 s k).
Proof. exact (fun_ext (fun f : _144007 -> _144038 => @lem8134413 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)). Qed.
Lemma lem8134415 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8134416 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term123 _144006 _144007 _144038 _144063 P h p P' lt2 s k) = (term163 _144006 _144007 _144038 _144063 P h p P' lt2 s k).
Proof. exact (MK_COMB (@lem8134415 _144007 _144038) (@lem8134414 _144006 _144007 _144038 _144063 P h p P' lt2 s k)). Qed.
Lemma lem8134421 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term103 _144006 _144007 _144038 _144063 P h p P' lt2 s k) = (term163 _144006 _144007 _144038 _144063 P h p P' lt2 s k).
Proof. exact (TRANS (@lem8134297 _144006 _144007 _144038 _144063 P h p P' lt2 s k) (@lem8134416 _144006 _144007 _144038 _144063 P h p P' lt2 s k)). Qed.
Lemma lem8134422 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term102 _144006 _144007 _144038 _144063 P h lt2 p P' s k) = (term163 _144006 _144007 _144038 _144063 P h p P' lt2 s k).
Proof. exact (TRANS (@lem8134270 _144006 _144007 _144038 _144063 P h p P' lt2 s k) (@lem8134421 _144006 _144007 _144038 _144063 P h p P' lt2 s k)). Qed.
Lemma lem8134423 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term164 _144006 _144007 _144038 _144063 P h lt2 p P' s k) = (term165 _144006 _144007 _144038 _144063 P h p P' lt2 s k).
Proof. exact (MK_COMB (@lem8133991 _144006 _144007 _144038 P p lt2 s P') (@lem8134422 _144006 _144007 _144038 _144063 P h p P' lt2 s k)). Qed.
Lemma lem8134425 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term8 A P Q) = (term9 A P Q).
Proof. exact (EQ_MP (@lem8133940 A P Q) (@lem8133939 A P Q)). Qed.
Lemma lem8134426 {_144007 _144038 : Type'} (P : type572 _144007 _144038) (Q : type572 _144007 _144038) : (term104 _144007 _144038 P Q) = (term105 _144007 _144038 P Q).
Proof. exact (@lem8134425 (_144007 -> _144038) P Q). Qed.
Lemma lem8134427 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term166 _144006 _144007 _144038 _144063 P h p P' lt2 s k) = (term167 _144006 _144007 _144038 _144063 P h p P' lt2 s k).
Proof. exact (@lem8134426 _144007 _144038 (term168 _144006 _144007 _144038 P p lt2 s P') (term162 _144006 _144007 _144038 _144063 P h p P' lt2 s k)). Qed.
Lemma lem8134428 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) : (term169 _144006 _144007 _144038 P p lt2 s P' f) = (term170 _144006 _144007 _144038 P p lt2 s f P').
Proof. exact (eq_refl (term169 _144006 _144007 _144038 P p lt2 s P' f)). Qed.
Lemma lem8134429 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (P' : type560 _144007 _144038 P) : (term171 _144006 _144007 _144038 P p lt2 s P') = (term168 _144006 _144007 _144038 P p lt2 s P').
Proof. exact (fun_ext (fun f : _144007 -> _144038 => @lem8134428 _144006 _144007 _144038 P p lt2 s f P')). Qed.
Lemma lem8134430 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8134431 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (P' : type560 _144007 _144038 P) : (term172 _144006 _144007 _144038 P p lt2 s P') = (term18 _144006 _144007 _144038 P p lt2 s P').
Proof. exact (MK_COMB (@lem8134430 _144007 _144038) (@lem8134429 _144006 _144007 _144038 P p lt2 s P')). Qed.
Lemma lem8134432 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134433 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (P' : type560 _144007 _144038 P) : (term173 _144006 _144007 _144038 P p lt2 s P') = (term20 _144006 _144007 _144038 P p lt2 s P').
Proof. exact (MK_COMB (@lem8134432) (@lem8134431 _144006 _144007 _144038 P p lt2 s P')). Qed.
Lemma lem8134434 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term174 _144006 _144007 _144038 _144063 P h p P' lt2 s k f) = (term161 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (eq_refl (term174 _144006 _144007 _144038 _144063 P h p P' lt2 s k f)). Qed.
Lemma lem8134435 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term175 _144006 _144007 _144038 _144063 P h p P' lt2 s k) = (term162 _144006 _144007 _144038 _144063 P h p P' lt2 s k).
Proof. exact (fun_ext (fun f : _144007 -> _144038 => @lem8134434 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)). Qed.
Lemma lem8134436 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8134437 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term176 _144006 _144007 _144038 _144063 P h p P' lt2 s k) = (term163 _144006 _144007 _144038 _144063 P h p P' lt2 s k).
Proof. exact (MK_COMB (@lem8134436 _144007 _144038) (@lem8134435 _144006 _144007 _144038 _144063 P h p P' lt2 s k)). Qed.
Lemma lem8134438 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term166 _144006 _144007 _144038 _144063 P h p P' lt2 s k) = (term165 _144006 _144007 _144038 _144063 P h p P' lt2 s k).
Proof. exact (MK_COMB (@lem8134433 _144006 _144007 _144038 P p lt2 s P') (@lem8134437 _144006 _144007 _144038 _144063 P h p P' lt2 s k)). Qed.
Lemma lem8134439 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8134440 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term177 _144006 _144007 _144038 _144063 P h p P' lt2 s k) = (term178 _144006 _144007 _144038 _144063 P h p P' lt2 s k).
Proof. exact (MK_COMB (@lem8134439) (@lem8134438 _144006 _144007 _144038 _144063 P h p P' lt2 s k)). Qed.
Lemma lem8134441 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) : (term169 _144006 _144007 _144038 P p lt2 s P' f) = (term170 _144006 _144007 _144038 P p lt2 s f P').
Proof. exact (eq_refl (term169 _144006 _144007 _144038 P p lt2 s P' f)). Qed.
Lemma lem8134442 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134443 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) : (term179 _144006 _144007 _144038 P p lt2 s P' f) = (term180 _144006 _144007 _144038 P p lt2 s f P').
Proof. exact (MK_COMB (@lem8134442) (@lem8134441 _144006 _144007 _144038 P p lt2 s f P')). Qed.
Lemma lem8134444 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term174 _144006 _144007 _144038 _144063 P h p P' lt2 s k f) = (term161 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (eq_refl (term174 _144006 _144007 _144038 _144063 P h p P' lt2 s k f)). Qed.
Lemma lem8134445 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term181 _144006 _144007 _144038 _144063 P h p P' lt2 s k f) = (term182 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (MK_COMB (@lem8134443 _144006 _144007 _144038 P p lt2 s f P') (@lem8134444 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)). Qed.
Lemma lem8134446 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term183 _144006 _144007 _144038 _144063 P h p P' lt2 s k) = (term184 _144006 _144007 _144038 _144063 P h p P' lt2 s k).
Proof. exact (fun_ext (fun f : _144007 -> _144038 => @lem8134445 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)). Qed.
Lemma lem8134447 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8134448 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term167 _144006 _144007 _144038 _144063 P h p P' lt2 s k) = (term185 _144006 _144007 _144038 _144063 P h p P' lt2 s k).
Proof. exact (MK_COMB (@lem8134447 _144007 _144038) (@lem8134446 _144006 _144007 _144038 _144063 P h p P' lt2 s k)). Qed.
Lemma lem8134449 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : ((term166 _144006 _144007 _144038 _144063 P h p P' lt2 s k) = (term167 _144006 _144007 _144038 _144063 P h p P' lt2 s k)) = ((term165 _144006 _144007 _144038 _144063 P h p P' lt2 s k) = (term185 _144006 _144007 _144038 _144063 P h p P' lt2 s k)).
Proof. exact (MK_COMB (@lem8134440 _144006 _144007 _144038 _144063 P h p P' lt2 s k) (@lem8134448 _144006 _144007 _144038 _144063 P h p P' lt2 s k)). Qed.
Lemma lem8134450 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term165 _144006 _144007 _144038 _144063 P h p P' lt2 s k) = (term185 _144006 _144007 _144038 _144063 P h p P' lt2 s k).
Proof. exact (EQ_MP (@lem8134449 _144006 _144007 _144038 _144063 P h p P' lt2 s k) (@lem8134427 _144006 _144007 _144038 _144063 P h p P' lt2 s k)). Qed.
Lemma lem8134456 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term8 A P Q) = (term9 A P Q).
Proof. exact (EQ_MP (@lem8133940 A P Q) (@lem8133939 A P Q)). Qed.
Lemma lem8134457 {_144007 _144038 : Type'} (P : type572 _144007 _144038) (Q : type572 _144007 _144038) : (term104 _144007 _144038 P Q) = (term105 _144007 _144038 P Q).
Proof. exact (@lem8134456 (_144007 -> _144038) P Q). Qed.
Lemma lem8134458 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term186 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) = (term187 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (@lem8134457 _144007 _144038 (term188 _144006 _144007 _144038 P p lt2 s f P') (term160 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)). Qed.
Lemma lem8134459 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) : (term189 _144006 _144007 _144038 P p lt2 s f P' g) = (term190 _144006 _144007 _144038 P p lt2 s f P' g).
Proof. exact (eq_refl (term189 _144006 _144007 _144038 P p lt2 s f P' g)). Qed.
Lemma lem8134460 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) : (term191 _144006 _144007 _144038 P p lt2 s f P') = (term188 _144006 _144007 _144038 P p lt2 s f P').
Proof. exact (fun_ext (fun g : _144007 -> _144038 => @lem8134459 _144006 _144007 _144038 P p lt2 s f P' g)). Qed.
Lemma lem8134461 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8134462 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) : (term192 _144006 _144007 _144038 P p lt2 s f P') = (term170 _144006 _144007 _144038 P p lt2 s f P').
Proof. exact (MK_COMB (@lem8134461 _144007 _144038) (@lem8134460 _144006 _144007 _144038 P p lt2 s f P')). Qed.
Lemma lem8134463 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134464 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) : (term193 _144006 _144007 _144038 P p lt2 s f P') = (term180 _144006 _144007 _144038 P p lt2 s f P').
Proof. exact (MK_COMB (@lem8134463) (@lem8134462 _144006 _144007 _144038 P p lt2 s f P')). Qed.
Lemma lem8134465 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term194 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) = (term159 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g).
Proof. exact (eq_refl (term194 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)). Qed.
Lemma lem8134466 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term195 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) = (term160 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (fun_ext (fun g : _144007 -> _144038 => @lem8134465 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)). Qed.
Lemma lem8134467 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8134468 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term196 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) = (term161 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (MK_COMB (@lem8134467 _144007 _144038) (@lem8134466 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)). Qed.
Lemma lem8134469 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term186 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) = (term182 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (MK_COMB (@lem8134464 _144006 _144007 _144038 P p lt2 s f P') (@lem8134468 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)). Qed.
Lemma lem8134470 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8134471 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term197 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) = (term198 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (MK_COMB (@lem8134470) (@lem8134469 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)). Qed.
Lemma lem8134472 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) : (term189 _144006 _144007 _144038 P p lt2 s f P' g) = (term190 _144006 _144007 _144038 P p lt2 s f P' g).
Proof. exact (eq_refl (term189 _144006 _144007 _144038 P p lt2 s f P' g)). Qed.
Lemma lem8134473 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134474 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) : (term199 _144006 _144007 _144038 P p lt2 s f P' g) = (term200 _144006 _144007 _144038 P p lt2 s f P' g).
Proof. exact (MK_COMB (@lem8134473) (@lem8134472 _144006 _144007 _144038 P p lt2 s f P' g)). Qed.
Lemma lem8134475 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term194 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) = (term159 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g).
Proof. exact (eq_refl (term194 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)). Qed.
Lemma lem8134476 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term201 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) = (term202 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g).
Proof. exact (MK_COMB (@lem8134474 _144006 _144007 _144038 P p lt2 s f P' g) (@lem8134475 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)). Qed.
Lemma lem8134477 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term203 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) = (term204 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (fun_ext (fun g : _144007 -> _144038 => @lem8134476 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)). Qed.
Lemma lem8134478 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8134479 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term187 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) = (term205 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (MK_COMB (@lem8134478 _144007 _144038) (@lem8134477 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)). Qed.
Lemma lem8134480 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : ((term186 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) = (term187 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)) = ((term182 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) = (term205 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)).
Proof. exact (MK_COMB (@lem8134471 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) (@lem8134479 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)). Qed.
Lemma lem8134481 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term182 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) = (term205 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (EQ_MP (@lem8134480 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) (@lem8134458 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)). Qed.
Lemma lem8134487 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term8 A P Q) = (term9 A P Q).
Proof. exact (EQ_MP (@lem8133940 A P Q) (@lem8133939 A P Q)). Qed.
Lemma lem8134488 {P : Type'} (P' : P -> Prop) (Q : P -> Prop) : (term8 P P' Q) = (term9 P P' Q).
Proof. exact (@lem8134487 P P' Q). Qed.
Lemma lem8134489 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term206 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) = (term207 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g).
Proof. exact (@lem8134488 P (term208 _144006 _144007 _144038 P p lt2 s f P' g) (term158 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)). Qed.
Lemma lem8134490 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term209 _144006 _144007 _144038 P p lt2 s f P' g a) = (term210 _144006 _144007 _144038 P p lt2 s f P' g a).
Proof. exact (eq_refl (term209 _144006 _144007 _144038 P p lt2 s f P' g a)). Qed.
Lemma lem8134491 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) : (term211 _144006 _144007 _144038 P p lt2 s f P' g) = (term208 _144006 _144007 _144038 P p lt2 s f P' g).
Proof. exact (fun_ext (fun a : P => @lem8134490 _144006 _144007 _144038 P p lt2 s f P' g a)). Qed.
Lemma lem8134492 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8134493 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) : (term212 _144006 _144007 _144038 P p lt2 s f P' g) = (term190 _144006 _144007 _144038 P p lt2 s f P' g).
Proof. exact (MK_COMB (@lem8134492 P) (@lem8134491 _144006 _144007 _144038 P p lt2 s f P' g)). Qed.
Lemma lem8134494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134495 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) : (term213 _144006 _144007 _144038 P p lt2 s f P' g) = (term200 _144006 _144007 _144038 P p lt2 s f P' g).
Proof. exact (MK_COMB (@lem8134494) (@lem8134493 _144006 _144007 _144038 P p lt2 s f P' g)). Qed.
Lemma lem8134496 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term214 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a) = (term156 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a).
Proof. exact (eq_refl (term214 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a)). Qed.
Lemma lem8134497 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term215 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) = (term158 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g).
Proof. exact (fun_ext (fun a : P => @lem8134496 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a)). Qed.
Lemma lem8134498 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8134499 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term216 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) = (term159 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g).
Proof. exact (MK_COMB (@lem8134498 P) (@lem8134497 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)). Qed.
Lemma lem8134500 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term206 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) = (term202 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g).
Proof. exact (MK_COMB (@lem8134495 _144006 _144007 _144038 P p lt2 s f P' g) (@lem8134499 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)). Qed.
Lemma lem8134501 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8134502 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term217 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) = (term218 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g).
Proof. exact (MK_COMB (@lem8134501) (@lem8134500 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)). Qed.
Lemma lem8134503 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term209 _144006 _144007 _144038 P p lt2 s f P' g a) = (term210 _144006 _144007 _144038 P p lt2 s f P' g a).
Proof. exact (eq_refl (term209 _144006 _144007 _144038 P p lt2 s f P' g a)). Qed.
Lemma lem8134504 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134505 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term219 _144006 _144007 _144038 P p lt2 s f P' g a) = (term220 _144006 _144007 _144038 P p lt2 s f P' g a).
Proof. exact (MK_COMB (@lem8134504) (@lem8134503 _144006 _144007 _144038 P p lt2 s f P' g a)). Qed.
Lemma lem8134506 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term214 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a) = (term156 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a).
Proof. exact (eq_refl (term214 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a)). Qed.
Lemma lem8134507 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term221 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a) = (term222 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a).
Proof. exact (MK_COMB (@lem8134505 _144006 _144007 _144038 P p lt2 s f P' g a) (@lem8134506 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a)). Qed.
Lemma lem8134508 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term223 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) = (term224 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g).
Proof. exact (fun_ext (fun a : P => @lem8134507 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a)). Qed.
Lemma lem8134509 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8134510 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term207 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) = (term225 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g).
Proof. exact (MK_COMB (@lem8134509 P) (@lem8134508 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)). Qed.
Lemma lem8134511 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : ((term206 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) = (term207 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)) = ((term202 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) = (term225 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)).
Proof. exact (MK_COMB (@lem8134502 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) (@lem8134510 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)). Qed.
Lemma lem8134512 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term202 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) = (term225 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g).
Proof. exact (EQ_MP (@lem8134511 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) (@lem8134489 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)). Qed.
Lemma lem8134577 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term204 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) = (term226 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (fun_ext (fun g : _144007 -> _144038 => @lem8134512 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)). Qed.
Lemma lem8134578 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8134579 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term205 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) = (term227 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (MK_COMB (@lem8134578 _144007 _144038) (@lem8134577 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)). Qed.
Lemma lem8134584 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term182 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) = (term227 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (TRANS (@lem8134481 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) (@lem8134579 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)). Qed.
Lemma lem8134585 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term184 _144006 _144007 _144038 _144063 P h p P' lt2 s k) = (term228 _144006 _144007 _144038 _144063 P h p P' lt2 s k).
Proof. exact (fun_ext (fun f : _144007 -> _144038 => @lem8134584 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)). Qed.
Lemma lem8134586 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8134587 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term185 _144006 _144007 _144038 _144063 P h p P' lt2 s k) = (term229 _144006 _144007 _144038 _144063 P h p P' lt2 s k).
Proof. exact (MK_COMB (@lem8134586 _144007 _144038) (@lem8134585 _144006 _144007 _144038 _144063 P h p P' lt2 s k)). Qed.
Lemma lem8134592 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term165 _144006 _144007 _144038 _144063 P h p P' lt2 s k) = (term229 _144006 _144007 _144038 _144063 P h p P' lt2 s k).
Proof. exact (TRANS (@lem8134450 _144006 _144007 _144038 _144063 P h p P' lt2 s k) (@lem8134587 _144006 _144007 _144038 _144063 P h p P' lt2 s k)). Qed.
Lemma lem8134593 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term164 _144006 _144007 _144038 _144063 P h lt2 p P' s k) = (term229 _144006 _144007 _144038 _144063 P h p P' lt2 s k).
Proof. exact (TRANS (@lem8134423 _144006 _144007 _144038 _144063 P h p P' lt2 s k) (@lem8134592 _144006 _144007 _144038 _144063 P h p P' lt2 s k)). Qed.
Lemma lem8134594 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8134595 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term230 _144006 _144007 _144038 _144063 P h lt2 p P' s k) = (term231 _144006 _144007 _144038 _144063 P h p P' lt2 s k).
Proof. exact (MK_COMB (@lem8134594) (@lem8134593 _144006 _144007 _144038 _144063 P h p P' lt2 s k)). Qed.
Lemma lem8134597 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term17 _143449 _143452 _143456 _143457 _143462 p lt2 s t).
Proof. exact (EQ_MP (@lem8133952 _143449 _143452 _143456 _143457 _143462 p lt2 s t) (@lem8133951 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8134598 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (t : type564 _144007 _144038 _144063 P) : (@admissible _144006 _144038 _144007 _144063 P lt2 p s t) = (term21 _144006 _144007 _144038 _144063 P p lt2 s t).
Proof. exact (@lem8134597 _144006 _144038 _144007 _144063 P p lt2 s t). Qed.
Lemma lem8134599 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : (term232 _144006 _144007 _144038 _144063 P lt2 p s P' h k) = (term233 _144006 _144007 _144038 _144063 P p lt2 s P' h k).
Proof. exact (@lem8134598 _144006 _144007 _144038 _144063 P p lt2 s (term234 _144007 _144038 _144063 P P' h k)). Qed.
Lemma lem8134629 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8134630 {_144007 _144038 _144063 P : Type'} (f : type564 _144007 _144038 _144063 P) (y : _144007 -> _144038) : (term235 _144007 _144038 _144063 P f y) = (f y).
Proof. exact (@lem8134629 (_144007 -> _144038) (P -> _144063) f y). Qed.
Lemma lem8134631 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) : (term236 _144007 _144038 _144063 P P' h k f) = (term237 _144007 _144038 _144063 P P' h k f).
Proof. exact (@lem8134630 _144007 _144038 _144063 P (term234 _144007 _144038 _144063 P P' h k) f). Qed.
Lemma lem8134632 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) : (term237 _144007 _144038 _144063 P P' h k f) = (term238 _144007 _144038 _144063 P P' h k f).
Proof. exact (eq_refl (term237 _144007 _144038 _144063 P P' h k f)). Qed.
Lemma lem8134633 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : (term239 _144007 _144038 _144063 P P' h k) = (term234 _144007 _144038 _144063 P P' h k).
Proof. exact (fun_ext (fun f : _144007 -> _144038 => @lem8134632 _144007 _144038 _144063 P P' h k f)). Qed.
Lemma lem8134634 {_144007 _144038 : Type'} (f : _144007 -> _144038) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8134635 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) : (term236 _144007 _144038 _144063 P P' h k f) = (term237 _144007 _144038 _144063 P P' h k f).
Proof. exact (MK_COMB (@lem8134633 _144007 _144038 _144063 P P' h k) (@lem8134634 _144007 _144038 f)). Qed.
Lemma lem8134636 {_144063 P : Type'} : (@eq (P -> _144063)) = (@eq (P -> _144063)).
Proof. exact (eq_refl (@eq (P -> _144063))). Qed.
Lemma lem8134637 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) : (term240 _144007 _144038 _144063 P P' h k f) = (term241 _144007 _144038 _144063 P P' h k f).
Proof. exact (MK_COMB (@lem8134636 _144063 P) (@lem8134635 _144007 _144038 _144063 P P' h k f)). Qed.
Lemma lem8134638 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) : (term237 _144007 _144038 _144063 P P' h k f) = (term238 _144007 _144038 _144063 P P' h k f).
Proof. exact (eq_refl (term237 _144007 _144038 _144063 P P' h k f)). Qed.
Lemma lem8134639 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) : ((term236 _144007 _144038 _144063 P P' h k f) = (term237 _144007 _144038 _144063 P P' h k f)) = ((term237 _144007 _144038 _144063 P P' h k f) = (term238 _144007 _144038 _144063 P P' h k f)).
Proof. exact (MK_COMB (@lem8134637 _144007 _144038 _144063 P P' h k f) (@lem8134638 _144007 _144038 _144063 P P' h k f)). Qed.
Lemma lem8134640 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) : (term237 _144007 _144038 _144063 P P' h k f) = (term238 _144007 _144038 _144063 P P' h k f).
Proof. exact (EQ_MP (@lem8134639 _144007 _144038 _144063 P P' h k f) (@lem8134631 _144007 _144038 _144063 P P' h k f)). Qed.
Lemma lem8134641 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8134642 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (a : P) : (term242 _144007 _144038 _144063 P P' h k f a) = (term243 _144007 _144038 _144063 P P' h k f a).
Proof. exact (MK_COMB (@lem8134640 _144007 _144038 _144063 P P' h k f) (@lem8134641 P a)). Qed.
Lemma lem8134644 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8134645 {_144063 P : Type'} (f : P -> _144063) (y : P) : (term244 _144063 P f y) = (f y).
Proof. exact (@lem8134644 P _144063 f y). Qed.
Lemma lem8134646 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (a : P) : (term245 _144007 _144038 _144063 P P' h k f a) = (term243 _144007 _144038 _144063 P P' h k f a).
Proof. exact (@lem8134645 _144063 P (term238 _144007 _144038 _144063 P P' h k f) a). Qed.
Lemma lem8134647 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (x : P) : (term243 _144007 _144038 _144063 P P' h k f x) = (term246 _144007 _144038 _144063 P P' h k f x).
Proof. exact (eq_refl (term243 _144007 _144038 _144063 P P' h k f x)). Qed.
Lemma lem8134648 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) : (term247 _144007 _144038 _144063 P P' h k f) = (term238 _144007 _144038 _144063 P P' h k f).
Proof. exact (fun_ext (fun x : P => @lem8134647 _144007 _144038 _144063 P P' h k f x)). Qed.
Lemma lem8134649 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8134650 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (a : P) : (term245 _144007 _144038 _144063 P P' h k f a) = (term243 _144007 _144038 _144063 P P' h k f a).
Proof. exact (MK_COMB (@lem8134648 _144007 _144038 _144063 P P' h k f) (@lem8134649 P a)). Qed.
Lemma lem8134651 {_144063 : Type'} : (@eq _144063) = (@eq _144063).
Proof. exact (eq_refl (@eq _144063)). Qed.
Lemma lem8134652 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (a : P) : (term248 _144007 _144038 _144063 P P' h k f a) = (term249 _144007 _144038 _144063 P P' h k f a).
Proof. exact (MK_COMB (@lem8134651 _144063) (@lem8134650 _144007 _144038 _144063 P P' h k f a)). Qed.
Lemma lem8134653 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (a : P) : (term243 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k f a).
Proof. exact (eq_refl (term243 _144007 _144038 _144063 P P' h k f a)). Qed.
Lemma lem8134654 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (a : P) : ((term245 _144007 _144038 _144063 P P' h k f a) = (term243 _144007 _144038 _144063 P P' h k f a)) = ((term243 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k f a)).
Proof. exact (MK_COMB (@lem8134652 _144007 _144038 _144063 P P' h k f a) (@lem8134653 _144007 _144038 _144063 P P' h k f a)). Qed.
Lemma lem8134655 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (a : P) : (term243 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k f a).
Proof. exact (EQ_MP (@lem8134654 _144007 _144038 _144063 P P' h k f a) (@lem8134646 _144007 _144038 _144063 P P' h k f a)). Qed.
Lemma lem8134656 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (a : P) : (term242 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k f a).
Proof. exact (TRANS (@lem8134642 _144007 _144038 _144063 P P' h k f a) (@lem8134655 _144007 _144038 _144063 P P' h k f a)). Qed.
Lemma lem8134657 {_144063 : Type'} : (@eq _144063) = (@eq _144063).
Proof. exact (eq_refl (@eq _144063)). Qed.
Lemma lem8134658 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (a : P) : (term250 _144007 _144038 _144063 P P' h k f a) = (term251 _144007 _144038 _144063 P P' h k f a).
Proof. exact (MK_COMB (@lem8134657 _144063) (@lem8134656 _144007 _144038 _144063 P P' h k f a)). Qed.
Lemma lem8134660 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8134661 {_144007 _144038 _144063 P : Type'} (f : type564 _144007 _144038 _144063 P) (y : _144007 -> _144038) : (term235 _144007 _144038 _144063 P f y) = (f y).
Proof. exact (@lem8134660 (_144007 -> _144038) (P -> _144063) f y). Qed.
Lemma lem8134662 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term236 _144007 _144038 _144063 P P' h k g) = (term237 _144007 _144038 _144063 P P' h k g).
Proof. exact (@lem8134661 _144007 _144038 _144063 P (term234 _144007 _144038 _144063 P P' h k) g). Qed.
Lemma lem8134663 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) : (term237 _144007 _144038 _144063 P P' h k f) = (term238 _144007 _144038 _144063 P P' h k f).
Proof. exact (eq_refl (term237 _144007 _144038 _144063 P P' h k f)). Qed.
Lemma lem8134664 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : (term239 _144007 _144038 _144063 P P' h k) = (term234 _144007 _144038 _144063 P P' h k).
Proof. exact (fun_ext (fun f : _144007 -> _144038 => @lem8134663 _144007 _144038 _144063 P P' h k f)). Qed.
Lemma lem8134665 {_144007 _144038 : Type'} (g : _144007 -> _144038) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8134666 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term236 _144007 _144038 _144063 P P' h k g) = (term237 _144007 _144038 _144063 P P' h k g).
Proof. exact (MK_COMB (@lem8134664 _144007 _144038 _144063 P P' h k) (@lem8134665 _144007 _144038 g)). Qed.
Lemma lem8134667 {_144063 P : Type'} : (@eq (P -> _144063)) = (@eq (P -> _144063)).
Proof. exact (eq_refl (@eq (P -> _144063))). Qed.
Lemma lem8134668 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term240 _144007 _144038 _144063 P P' h k g) = (term241 _144007 _144038 _144063 P P' h k g).
Proof. exact (MK_COMB (@lem8134667 _144063 P) (@lem8134666 _144007 _144038 _144063 P P' h k g)). Qed.
Lemma lem8134669 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term237 _144007 _144038 _144063 P P' h k g) = (term238 _144007 _144038 _144063 P P' h k g).
Proof. exact (eq_refl (term237 _144007 _144038 _144063 P P' h k g)). Qed.
Lemma lem8134670 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : ((term236 _144007 _144038 _144063 P P' h k g) = (term237 _144007 _144038 _144063 P P' h k g)) = ((term237 _144007 _144038 _144063 P P' h k g) = (term238 _144007 _144038 _144063 P P' h k g)).
Proof. exact (MK_COMB (@lem8134668 _144007 _144038 _144063 P P' h k g) (@lem8134669 _144007 _144038 _144063 P P' h k g)). Qed.
Lemma lem8134671 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term237 _144007 _144038 _144063 P P' h k g) = (term238 _144007 _144038 _144063 P P' h k g).
Proof. exact (EQ_MP (@lem8134670 _144007 _144038 _144063 P P' h k g) (@lem8134662 _144007 _144038 _144063 P P' h k g)). Qed.
Lemma lem8134672 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8134673 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term242 _144007 _144038 _144063 P P' h k g a) = (term243 _144007 _144038 _144063 P P' h k g a).
Proof. exact (MK_COMB (@lem8134671 _144007 _144038 _144063 P P' h k g) (@lem8134672 P a)). Qed.
Lemma lem8134675 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8134676 {_144063 P : Type'} (f : P -> _144063) (y : P) : (term244 _144063 P f y) = (f y).
Proof. exact (@lem8134675 P _144063 f y). Qed.
Lemma lem8134677 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term245 _144007 _144038 _144063 P P' h k g a) = (term243 _144007 _144038 _144063 P P' h k g a).
Proof. exact (@lem8134676 _144063 P (term238 _144007 _144038 _144063 P P' h k g) a). Qed.
Lemma lem8134678 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (x : P) : (term243 _144007 _144038 _144063 P P' h k g x) = (term246 _144007 _144038 _144063 P P' h k g x).
Proof. exact (eq_refl (term243 _144007 _144038 _144063 P P' h k g x)). Qed.
Lemma lem8134679 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term247 _144007 _144038 _144063 P P' h k g) = (term238 _144007 _144038 _144063 P P' h k g).
Proof. exact (fun_ext (fun x : P => @lem8134678 _144007 _144038 _144063 P P' h k g x)). Qed.
Lemma lem8134680 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8134681 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term245 _144007 _144038 _144063 P P' h k g a) = (term243 _144007 _144038 _144063 P P' h k g a).
Proof. exact (MK_COMB (@lem8134679 _144007 _144038 _144063 P P' h k g) (@lem8134680 P a)). Qed.
Lemma lem8134682 {_144063 : Type'} : (@eq _144063) = (@eq _144063).
Proof. exact (eq_refl (@eq _144063)). Qed.
Lemma lem8134683 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term248 _144007 _144038 _144063 P P' h k g a) = (term249 _144007 _144038 _144063 P P' h k g a).
Proof. exact (MK_COMB (@lem8134682 _144063) (@lem8134681 _144007 _144038 _144063 P P' h k g a)). Qed.
Lemma lem8134684 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term243 _144007 _144038 _144063 P P' h k g a) = (term246 _144007 _144038 _144063 P P' h k g a).
Proof. exact (eq_refl (term243 _144007 _144038 _144063 P P' h k g a)). Qed.
Lemma lem8134685 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : ((term245 _144007 _144038 _144063 P P' h k g a) = (term243 _144007 _144038 _144063 P P' h k g a)) = ((term243 _144007 _144038 _144063 P P' h k g a) = (term246 _144007 _144038 _144063 P P' h k g a)).
Proof. exact (MK_COMB (@lem8134683 _144007 _144038 _144063 P P' h k g a) (@lem8134684 _144007 _144038 _144063 P P' h k g a)). Qed.
Lemma lem8134686 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term243 _144007 _144038 _144063 P P' h k g a) = (term246 _144007 _144038 _144063 P P' h k g a).
Proof. exact (EQ_MP (@lem8134685 _144007 _144038 _144063 P P' h k g a) (@lem8134677 _144007 _144038 _144063 P P' h k g a)). Qed.
Lemma lem8134687 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term242 _144007 _144038 _144063 P P' h k g a) = (term246 _144007 _144038 _144063 P P' h k g a).
Proof. exact (TRANS (@lem8134673 _144007 _144038 _144063 P P' h k g a) (@lem8134686 _144007 _144038 _144063 P P' h k g a)). Qed.
Lemma lem8134688 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : ((term242 _144007 _144038 _144063 P P' h k f a) = (term242 _144007 _144038 _144063 P P' h k g a)) = ((term246 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k g a)).
Proof. exact (MK_COMB (@lem8134658 _144007 _144038 _144063 P P' h k f a) (@lem8134687 _144007 _144038 _144063 P P' h k g a)). Qed.
Lemma lem8134691 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) : (term252 _144006 _144007 _144038 P p lt2 s a f g) = (term252 _144006 _144007 _144038 P p lt2 s a f g).
Proof. exact (eq_refl (term252 _144006 _144007 _144038 P p lt2 s a f g)). Qed.
Lemma lem8134692 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term253 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a) = (term254 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a).
Proof. exact (MK_COMB (@lem8134691 _144006 _144007 _144038 P p lt2 s a f g) (@lem8134688 _144007 _144038 _144063 P f P' h k g a)). Qed.
Lemma lem8134695 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term255 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g) = (term256 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g).
Proof. exact (fun_ext (fun a : P => @lem8134692 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a)). Qed.
Lemma lem8134696 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8134697 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term257 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g) = (term258 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g).
Proof. exact (MK_COMB (@lem8134696 P) (@lem8134695 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g)). Qed.
Lemma lem8134702 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : (term259 _144006 _144007 _144038 _144063 P p lt2 s f P' h k) = (term260 _144006 _144007 _144038 _144063 P p lt2 s f P' h k).
Proof. exact (fun_ext (fun g : _144007 -> _144038 => @lem8134697 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g)). Qed.
Lemma lem8134703 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8134704 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : (term261 _144006 _144007 _144038 _144063 P p lt2 s f P' h k) = (term262 _144006 _144007 _144038 _144063 P p lt2 s f P' h k).
Proof. exact (MK_COMB (@lem8134703 _144007 _144038) (@lem8134702 _144006 _144007 _144038 _144063 P p lt2 s f P' h k)). Qed.
Lemma lem8134709 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : (term263 _144006 _144007 _144038 _144063 P p lt2 s P' h k) = (term264 _144006 _144007 _144038 _144063 P p lt2 s P' h k).
Proof. exact (fun_ext (fun f : _144007 -> _144038 => @lem8134704 _144006 _144007 _144038 _144063 P p lt2 s f P' h k)). Qed.
Lemma lem8134710 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8134711 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : (term233 _144006 _144007 _144038 _144063 P p lt2 s P' h k) = (term265 _144006 _144007 _144038 _144063 P p lt2 s P' h k).
Proof. exact (MK_COMB (@lem8134710 _144007 _144038) (@lem8134709 _144006 _144007 _144038 _144063 P p lt2 s P' h k)). Qed.
Lemma lem8134716 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : (term232 _144006 _144007 _144038 _144063 P lt2 p s P' h k) = (term265 _144006 _144007 _144038 _144063 P p lt2 s P' h k).
Proof. exact (TRANS (@lem8134599 _144006 _144007 _144038 _144063 P p lt2 s P' h k) (@lem8134711 _144006 _144007 _144038 _144063 P p lt2 s P' h k)). Qed.
Lemma lem8134717 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : (term266 _144006 _144007 _144038 _144063 P lt2 p s P' h k) = (term267 _144006 _144007 _144038 _144063 P p lt2 s P' h k).
Proof. exact (MK_COMB (@lem8134595 _144006 _144007 _144038 _144063 P h p P' lt2 s k) (@lem8134716 _144006 _144007 _144038 _144063 P p lt2 s P' h k)). Qed.
Lemma lem8134720 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (p : type560 _144007 _144038 P) (s : P -> _144006) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : (term267 _144006 _144007 _144038 _144063 P p lt2 s P' h k) = (term266 _144006 _144007 _144038 _144063 P lt2 p s P' h k).
Proof. exact (SYM (@lem8134717 _144006 _144007 _144038 _144063 P p lt2 s P' h k)). Qed.
Lemma lem8134722 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term0 A P Q.
Proof. exact (@lem8133934 A P Q (@lem7363 A P Q)). Qed.
Lemma lem8134723 {_144007 _144038 : Type'} (P : type572 _144007 _144038) (Q : type572 _144007 _144038) : term268 _144007 _144038 P Q.
Proof. exact (@lem8134722 (_144007 -> _144038) P Q). Qed.
Lemma lem8134724 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : term269 _144006 _144007 _144038 _144063 P p lt2 s P' h k.
Proof. exact (@lem8134723 _144007 _144038 (term228 _144006 _144007 _144038 _144063 P h p P' lt2 s k) (term264 _144006 _144007 _144038 _144063 P p lt2 s P' h k)). Qed.
Lemma lem8134725 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term270 _144006 _144007 _144038 _144063 P h p P' lt2 s k f) = (term227 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (eq_refl (term270 _144006 _144007 _144038 _144063 P h p P' lt2 s k f)). Qed.
Lemma lem8134726 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8134727 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term271 _144006 _144007 _144038 _144063 P h p P' lt2 s k f) = (term272 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (MK_COMB (@lem8134726) (@lem8134725 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)). Qed.
Lemma lem8134728 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : (term273 _144006 _144007 _144038 _144063 P p lt2 s P' h k f) = (term262 _144006 _144007 _144038 _144063 P p lt2 s f P' h k).
Proof. exact (eq_refl (term273 _144006 _144007 _144038 _144063 P p lt2 s P' h k f)). Qed.
Lemma lem8134729 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : (term274 _144006 _144007 _144038 _144063 P p lt2 s P' h k f) = (term275 _144006 _144007 _144038 _144063 P p lt2 s f P' h k).
Proof. exact (MK_COMB (@lem8134727 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) (@lem8134728 _144006 _144007 _144038 _144063 P p lt2 s f P' h k)). Qed.
Lemma lem8134730 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : (term276 _144006 _144007 _144038 _144063 P p lt2 s P' h k) = (term277 _144006 _144007 _144038 _144063 P p lt2 s P' h k).
Proof. exact (fun_ext (fun f : _144007 -> _144038 => @lem8134729 _144006 _144007 _144038 _144063 P p lt2 s f P' h k)). Qed.
Lemma lem8134731 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8134732 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : (term278 _144006 _144007 _144038 _144063 P p lt2 s P' h k) = (term279 _144006 _144007 _144038 _144063 P p lt2 s P' h k).
Proof. exact (MK_COMB (@lem8134731 _144007 _144038) (@lem8134730 _144006 _144007 _144038 _144063 P p lt2 s P' h k)). Qed.
Lemma lem8134733 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8134734 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : (term280 _144006 _144007 _144038 _144063 P p lt2 s P' h k) = (term281 _144006 _144007 _144038 _144063 P p lt2 s P' h k).
Proof. exact (MK_COMB (@lem8134733) (@lem8134732 _144006 _144007 _144038 _144063 P p lt2 s P' h k)). Qed.
Lemma lem8134735 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term270 _144006 _144007 _144038 _144063 P h p P' lt2 s k f) = (term227 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (eq_refl (term270 _144006 _144007 _144038 _144063 P h p P' lt2 s k f)). Qed.
Lemma lem8134736 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term282 _144006 _144007 _144038 _144063 P h p P' lt2 s k) = (term228 _144006 _144007 _144038 _144063 P h p P' lt2 s k).
Proof. exact (fun_ext (fun f : _144007 -> _144038 => @lem8134735 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)). Qed.
Lemma lem8134737 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8134738 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term283 _144006 _144007 _144038 _144063 P h p P' lt2 s k) = (term229 _144006 _144007 _144038 _144063 P h p P' lt2 s k).
Proof. exact (MK_COMB (@lem8134737 _144007 _144038) (@lem8134736 _144006 _144007 _144038 _144063 P h p P' lt2 s k)). Qed.
Lemma lem8134739 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8134740 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) : (term284 _144006 _144007 _144038 _144063 P h p P' lt2 s k) = (term231 _144006 _144007 _144038 _144063 P h p P' lt2 s k).
Proof. exact (MK_COMB (@lem8134739) (@lem8134738 _144006 _144007 _144038 _144063 P h p P' lt2 s k)). Qed.
Lemma lem8134741 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : (term273 _144006 _144007 _144038 _144063 P p lt2 s P' h k f) = (term262 _144006 _144007 _144038 _144063 P p lt2 s f P' h k).
Proof. exact (eq_refl (term273 _144006 _144007 _144038 _144063 P p lt2 s P' h k f)). Qed.
Lemma lem8134742 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : (term285 _144006 _144007 _144038 _144063 P p lt2 s P' h k) = (term264 _144006 _144007 _144038 _144063 P p lt2 s P' h k).
Proof. exact (fun_ext (fun f : _144007 -> _144038 => @lem8134741 _144006 _144007 _144038 _144063 P p lt2 s f P' h k)). Qed.
Lemma lem8134743 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8134744 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : (term286 _144006 _144007 _144038 _144063 P p lt2 s P' h k) = (term265 _144006 _144007 _144038 _144063 P p lt2 s P' h k).
Proof. exact (MK_COMB (@lem8134743 _144007 _144038) (@lem8134742 _144006 _144007 _144038 _144063 P p lt2 s P' h k)). Qed.
Lemma lem8134745 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : (term287 _144006 _144007 _144038 _144063 P p lt2 s P' h k) = (term267 _144006 _144007 _144038 _144063 P p lt2 s P' h k).
Proof. exact (MK_COMB (@lem8134740 _144006 _144007 _144038 _144063 P h p P' lt2 s k) (@lem8134744 _144006 _144007 _144038 _144063 P p lt2 s P' h k)). Qed.
Lemma lem8134746 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : (term269 _144006 _144007 _144038 _144063 P p lt2 s P' h k) = (term288 _144006 _144007 _144038 _144063 P p lt2 s P' h k).
Proof. exact (MK_COMB (@lem8134734 _144006 _144007 _144038 _144063 P p lt2 s P' h k) (@lem8134745 _144006 _144007 _144038 _144063 P p lt2 s P' h k)). Qed.
Lemma lem8134747 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : term288 _144006 _144007 _144038 _144063 P p lt2 s P' h k.
Proof. exact (EQ_MP (@lem8134746 _144006 _144007 _144038 _144063 P p lt2 s P' h k) (@lem8134724 _144006 _144007 _144038 _144063 P p lt2 s P' h k)). Qed.
Lemma lem8134749 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term0 A P Q.
Proof. exact (@lem8133934 A P Q (@lem7363 A P Q)). Qed.
Lemma lem8134750 {_144007 _144038 : Type'} (P : type572 _144007 _144038) (Q : type572 _144007 _144038) : term268 _144007 _144038 P Q.
Proof. exact (@lem8134749 (_144007 -> _144038) P Q). Qed.
Lemma lem8134751 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : term289 _144006 _144007 _144038 _144063 P p lt2 s f P' h k.
Proof. exact (@lem8134750 _144007 _144038 (term226 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) (term260 _144006 _144007 _144038 _144063 P p lt2 s f P' h k)). Qed.
Lemma lem8134752 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term290 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) = (term225 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g).
Proof. exact (eq_refl (term290 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)). Qed.
Lemma lem8134753 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8134754 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term291 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) = (term292 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g).
Proof. exact (MK_COMB (@lem8134753) (@lem8134752 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)). Qed.
Lemma lem8134755 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term293 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g) = (term258 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g).
Proof. exact (eq_refl (term293 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g)). Qed.
Lemma lem8134756 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term294 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g) = (term295 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g).
Proof. exact (MK_COMB (@lem8134754 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) (@lem8134755 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g)). Qed.
Lemma lem8134757 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : (term296 _144006 _144007 _144038 _144063 P p lt2 s f P' h k) = (term297 _144006 _144007 _144038 _144063 P p lt2 s f P' h k).
Proof. exact (fun_ext (fun g : _144007 -> _144038 => @lem8134756 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g)). Qed.
Lemma lem8134758 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8134759 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : (term298 _144006 _144007 _144038 _144063 P p lt2 s f P' h k) = (term299 _144006 _144007 _144038 _144063 P p lt2 s f P' h k).
Proof. exact (MK_COMB (@lem8134758 _144007 _144038) (@lem8134757 _144006 _144007 _144038 _144063 P p lt2 s f P' h k)). Qed.
Lemma lem8134760 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8134761 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : (term300 _144006 _144007 _144038 _144063 P p lt2 s f P' h k) = (term301 _144006 _144007 _144038 _144063 P p lt2 s f P' h k).
Proof. exact (MK_COMB (@lem8134760) (@lem8134759 _144006 _144007 _144038 _144063 P p lt2 s f P' h k)). Qed.
Lemma lem8134762 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term290 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) = (term225 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g).
Proof. exact (eq_refl (term290 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)). Qed.
Lemma lem8134763 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term302 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) = (term226 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (fun_ext (fun g : _144007 -> _144038 => @lem8134762 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)). Qed.
Lemma lem8134764 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8134765 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term303 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) = (term227 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (MK_COMB (@lem8134764 _144007 _144038) (@lem8134763 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)). Qed.
Lemma lem8134766 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8134767 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) : (term304 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) = (term272 _144006 _144007 _144038 _144063 P h p P' lt2 s f k).
Proof. exact (MK_COMB (@lem8134766) (@lem8134765 _144006 _144007 _144038 _144063 P h p P' lt2 s f k)). Qed.
Lemma lem8134768 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term293 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g) = (term258 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g).
Proof. exact (eq_refl (term293 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g)). Qed.
Lemma lem8134769 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : (term305 _144006 _144007 _144038 _144063 P p lt2 s f P' h k) = (term260 _144006 _144007 _144038 _144063 P p lt2 s f P' h k).
Proof. exact (fun_ext (fun g : _144007 -> _144038 => @lem8134768 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g)). Qed.
Lemma lem8134770 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8134771 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : (term306 _144006 _144007 _144038 _144063 P p lt2 s f P' h k) = (term262 _144006 _144007 _144038 _144063 P p lt2 s f P' h k).
Proof. exact (MK_COMB (@lem8134770 _144007 _144038) (@lem8134769 _144006 _144007 _144038 _144063 P p lt2 s f P' h k)). Qed.
Lemma lem8134772 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : (term307 _144006 _144007 _144038 _144063 P p lt2 s f P' h k) = (term275 _144006 _144007 _144038 _144063 P p lt2 s f P' h k).
Proof. exact (MK_COMB (@lem8134767 _144006 _144007 _144038 _144063 P h p P' lt2 s f k) (@lem8134771 _144006 _144007 _144038 _144063 P p lt2 s f P' h k)). Qed.
Lemma lem8134773 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : (term289 _144006 _144007 _144038 _144063 P p lt2 s f P' h k) = (term308 _144006 _144007 _144038 _144063 P p lt2 s f P' h k).
Proof. exact (MK_COMB (@lem8134761 _144006 _144007 _144038 _144063 P p lt2 s f P' h k) (@lem8134772 _144006 _144007 _144038 _144063 P p lt2 s f P' h k)). Qed.
Lemma lem8134774 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : term308 _144006 _144007 _144038 _144063 P p lt2 s f P' h k.
Proof. exact (EQ_MP (@lem8134773 _144006 _144007 _144038 _144063 P p lt2 s f P' h k) (@lem8134751 _144006 _144007 _144038 _144063 P p lt2 s f P' h k)). Qed.
Lemma lem8134776 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term0 A P Q.
Proof. exact (@lem8133934 A P Q (@lem7363 A P Q)). Qed.
Lemma lem8134777 {P : Type'} (P' : P -> Prop) (Q : P -> Prop) : term0 P P' Q.
Proof. exact (@lem8134776 P P' Q). Qed.
Lemma lem8134778 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : term309 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g.
Proof. exact (@lem8134777 P (term224 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) (term256 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g)). Qed.
Lemma lem8134779 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term310 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a) = (term222 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a).
Proof. exact (eq_refl (term310 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a)). Qed.
Lemma lem8134780 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8134781 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term311 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a) = (term312 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a).
Proof. exact (MK_COMB (@lem8134780) (@lem8134779 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a)). Qed.
Lemma lem8134782 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term313 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a) = (term254 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a).
Proof. exact (eq_refl (term313 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a)). Qed.
Lemma lem8134783 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term314 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a) = (term315 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a).
Proof. exact (MK_COMB (@lem8134781 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a) (@lem8134782 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a)). Qed.
Lemma lem8134784 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term316 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g) = (term317 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g).
Proof. exact (fun_ext (fun a : P => @lem8134783 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a)). Qed.
Lemma lem8134785 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8134786 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term318 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g) = (term319 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g).
Proof. exact (MK_COMB (@lem8134785 P) (@lem8134784 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g)). Qed.
Lemma lem8134787 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8134788 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term320 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g) = (term321 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g).
Proof. exact (MK_COMB (@lem8134787) (@lem8134786 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g)). Qed.
Lemma lem8134789 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term310 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a) = (term222 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a).
Proof. exact (eq_refl (term310 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a)). Qed.
Lemma lem8134790 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term322 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) = (term224 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g).
Proof. exact (fun_ext (fun a : P => @lem8134789 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a)). Qed.
Lemma lem8134791 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8134792 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term323 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) = (term225 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g).
Proof. exact (MK_COMB (@lem8134791 P) (@lem8134790 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)). Qed.
Lemma lem8134793 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8134794 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term324 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) = (term292 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g).
Proof. exact (MK_COMB (@lem8134793) (@lem8134792 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g)). Qed.
Lemma lem8134795 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term313 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a) = (term254 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a).
Proof. exact (eq_refl (term313 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a)). Qed.
Lemma lem8134796 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term325 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g) = (term256 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g).
Proof. exact (fun_ext (fun a : P => @lem8134795 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a)). Qed.
Lemma lem8134797 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8134798 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term326 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g) = (term258 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g).
Proof. exact (MK_COMB (@lem8134797 P) (@lem8134796 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g)). Qed.
Lemma lem8134799 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term327 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g) = (term295 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g).
Proof. exact (MK_COMB (@lem8134794 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g) (@lem8134798 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g)). Qed.
Lemma lem8134800 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : (term309 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g) = (term328 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g).
Proof. exact (MK_COMB (@lem8134788 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g) (@lem8134799 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g)). Qed.
Lemma lem8134801 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : term328 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g.
Proof. exact (EQ_MP (@lem8134800 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g) (@lem8134778 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g)). Qed.
Lemma lem8134804 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) (h1 : term222 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a) : term222 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a.
Proof. exact (h1). Qed.
Lemma lem8134805 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) (h1 : term329 _144006 _144007 _144038 P p lt2 s a f g) : term329 _144006 _144007 _144038 P p lt2 s a f g.
Proof. exact (h1). Qed.
Lemma lem8134806 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) (h1 : term330 _144006 _144007 _144038 P p lt2 s a f g) : term330 _144006 _144007 _144038 P p lt2 s a f g.
Proof. exact (h1). Qed.
Lemma lem8134807 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : p f a) : p f a.
Proof. exact (h1). Qed.
Lemma lem8134808 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) : term43 _144006 _144007 _144038 P lt2 s a f g.
Proof. exact (h1). Qed.
Lemma lem8134809 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : p g a) : p g a.
Proof. exact (h1). Qed.
Lemma lem8134810 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (p f a) = ((p f a) = True).
Proof. exact (@lem7 (p f a)). Qed.
Lemma lem8134812 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (p g a) = ((p g a) = True).
Proof. exact (@lem7 (p g a)). Qed.
Lemma lem8134814 {_144006 _144007 _144038 P : Type'} (z : _144007) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) : term331 _144006 _144007 _144038 P lt2 s a f g z.
Proof. exact (@lem8134808 _144006 _144007 _144038 P lt2 s a f g h1 z). Qed.
Lemma lem8134815 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) (z : _144007) : (term331 _144006 _144007 _144038 P lt2 s a f g z) = (term332 _144006 _144007 _144038 P lt2 s a f g z).
Proof. exact (eq_refl (term331 _144006 _144007 _144038 P lt2 s a f g z)). Qed.
Lemma lem8134816 {_144006 _144007 _144038 P : Type'} (z : _144007) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) : term332 _144006 _144007 _144038 P lt2 s a f g z.
Proof. exact (EQ_MP (@lem8134815 _144006 _144007 _144038 P lt2 s a f g z) (@lem8134814 _144006 _144007 _144038 P z lt2 s a f g h1)). Qed.
Lemma lem8134817 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) (z : _144007) : (term332 _144006 _144007 _144038 P lt2 s a f g z) = ((term332 _144006 _144007 _144038 P lt2 s a f g z) = True).
Proof. exact (@lem7 (term332 _144006 _144007 _144038 P lt2 s a f g z)). Qed.
Lemma lem8134828 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : p f a) : (p f a) = True.
Proof. exact (EQ_MP (@lem8134810 _144007 _144038 P p f a) (@lem8134807 _144007 _144038 P p f a h1)). Qed.
Lemma lem8134829 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134830 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : p f a) : (term333 _144007 _144038 P p f a) = (and True).
Proof. exact (MK_COMB (@lem8134829) (@lem8134828 _144007 _144038 P p f a h1)). Qed.
Lemma lem8134834 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : p g a) : (p g a) = True.
Proof. exact (EQ_MP (@lem8134812 _144007 _144038 P p g a) (@lem8134809 _144007 _144038 P p g a h1)). Qed.
Lemma lem8134835 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134836 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : p g a) : (term333 _144007 _144038 P p g a) = (and True).
Proof. exact (MK_COMB (@lem8134835) (@lem8134834 _144007 _144038 P p g a h1)). Qed.
Lemma lem8134842 {_144006 _144007 _144038 P : Type'} (z : _144007) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) : (term332 _144006 _144007 _144038 P lt2 s a f g z) = True.
Proof. exact (EQ_MP (@lem8134817 _144006 _144007 _144038 P lt2 s a f g z) (@lem8134816 _144006 _144007 _144038 P z lt2 s a f g h1)). Qed.
Lemma lem8134843 {_144006 _144007 _144038 P : Type'} (z : _144007) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) : (term332 _144006 _144007 _144038 P lt2 s a f g z) = True.
Proof. exact (@lem8134842 _144006 _144007 _144038 P z lt2 s a f g h1). Qed.
Lemma lem8134844 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) : (term334 _144006 _144007 _144038 P lt2 s a f g) = (term335 _144007).
Proof. exact (fun_ext (fun z : _144007 => @lem8134843 _144006 _144007 _144038 P z lt2 s a f g h1)). Qed.
Lemma lem8134845 {_144007 : Type'} : (@all _144007) = (@all _144007).
Proof. exact (eq_refl (@all _144007)). Qed.
Lemma lem8134846 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) : (term43 _144006 _144007 _144038 P lt2 s a f g) = (term336 _144007).
Proof. exact (MK_COMB (@lem8134845 _144007) (@lem8134844 _144006 _144007 _144038 P lt2 s a f g h1)). Qed.
Lemma lem8134848 {A : Type'} (t : Prop) : (term337 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8134849 {_144007 : Type'} (t : Prop) : (term337 _144007 t) = t.
Proof. exact (@lem8134848 _144007 t). Qed.
Lemma lem8134850 {_144007 : Type'} : (term336 _144007) = True.
Proof. exact (@lem8134849 _144007 True). Qed.
Lemma lem8134851 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) : (term43 _144006 _144007 _144038 P lt2 s a f g) = True.
Proof. exact (TRANS (@lem8134846 _144006 _144007 _144038 P lt2 s a f g h1) (@lem8134850 _144007)). Qed.
Lemma lem8134852 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : p g a) : (term330 _144006 _144007 _144038 P p lt2 s a f g) = (True /\ True).
Proof. exact (MK_COMB (@lem8134836 _144007 _144038 P p g a h2) (@lem8134851 _144006 _144007 _144038 P lt2 s a f g h1)). Qed.
Lemma lem8134854 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8134855 : (True /\ True) = True.
Proof. exact (@lem8134854 True). Qed.
Lemma lem8134856 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : p g a) : (term330 _144006 _144007 _144038 P p lt2 s a f g) = True.
Proof. exact (TRANS (@lem8134852 _144006 _144007 _144038 P lt2 s f p g a h1 h2) (@lem8134855)). Qed.
Lemma lem8134857 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : p f a) (h3 : p g a) : (term329 _144006 _144007 _144038 P p lt2 s a f g) = (True /\ True).
Proof. exact (MK_COMB (@lem8134830 _144007 _144038 P p f a h2) (@lem8134856 _144006 _144007 _144038 P lt2 s f p g a h1 h3)). Qed.
Lemma lem8134859 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8134860 : (True /\ True) = True.
Proof. exact (@lem8134859 True). Qed.
Lemma lem8134861 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : p f a) (h3 : p g a) : (term329 _144006 _144007 _144038 P p lt2 s a f g) = True.
Proof. exact (TRANS (@lem8134857 _144006 _144007 _144038 P lt2 s f p g a h1 h2 h3) (@lem8134860)). Qed.
Lemma lem8134862 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8134863 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : p f a) (h3 : p g a) : (term252 _144006 _144007 _144038 P p lt2 s a f g) = (imp True).
Proof. exact (MK_COMB (@lem8134862) (@lem8134861 _144006 _144007 _144038 P lt2 s f p g a h1 h2 h3)). Qed.
Lemma lem8134866 {_144007 _144038 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : ((P' f a) = (P' g a)) = ((P' f a) = (P' g a)).
Proof. exact (eq_refl ((P' f a) = (P' g a))). Qed.
Lemma lem8134867 {_144006 _144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : p f a) (h3 : p g a) : (term210 _144006 _144007 _144038 P p lt2 s f P' g a) = (term338 _144007 _144038 P f P' g a).
Proof. exact (MK_COMB (@lem8134863 _144006 _144007 _144038 P lt2 s f p g a h1 h2 h3) (@lem8134866 _144007 _144038 P f P' g a)). Qed.
Lemma lem8134869 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem8134870 {_144007 _144038 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term338 _144007 _144038 P f P' g a) = ((P' f a) = (P' g a)).
Proof. exact (@lem8134869 ((P' f a) = (P' g a))). Qed.
Lemma lem8134873 {_144006 _144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : p f a) (h3 : p g a) : (term210 _144006 _144007 _144038 P p lt2 s f P' g a) = ((P' f a) = (P' g a)).
Proof. exact (TRANS (@lem8134867 _144006 _144007 _144038 P P' lt2 s f p g a h1 h2 h3) (@lem8134870 _144007 _144038 P f P' g a)). Qed.
Lemma lem8134874 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134875 {_144006 _144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : p f a) (h3 : p g a) : (term220 _144006 _144007 _144038 P p lt2 s f P' g a) = (term339 _144007 _144038 P f P' g a).
Proof. exact (MK_COMB (@lem8134874) (@lem8134873 _144006 _144007 _144038 P P' lt2 s f p g a h1 h2 h3)). Qed.
Lemma lem8134885 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : p f a) : (p f a) = True.
Proof. exact (EQ_MP (@lem8134810 _144007 _144038 P p f a) (@lem8134807 _144007 _144038 P p f a h1)). Qed.
Lemma lem8134886 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134887 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : p f a) : (term333 _144007 _144038 P p f a) = (and True).
Proof. exact (MK_COMB (@lem8134886) (@lem8134885 _144007 _144038 P p f a h1)). Qed.
Lemma lem8134888 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (P' f a) = (P' f a).
Proof. exact (eq_refl (P' f a)). Qed.
Lemma lem8134889 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : p f a) : (term37 _144007 _144038 P p P' f a) = (term340 _144007 _144038 P P' f a).
Proof. exact (MK_COMB (@lem8134887 _144007 _144038 P p f a h1) (@lem8134888 _144007 _144038 P P' f a)). Qed.
Lemma lem8134891 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8134892 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term340 _144007 _144038 P P' f a) = (P' f a).
Proof. exact (@lem8134891 (P' f a)). Qed.
Lemma lem8134893 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : p f a) : (term37 _144007 _144038 P p P' f a) = (P' f a).
Proof. exact (TRANS (@lem8134889 _144007 _144038 P P' p f a h1) (@lem8134892 _144007 _144038 P P' f a)). Qed.
Lemma lem8134894 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134895 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : p f a) : (term42 _144007 _144038 P p P' f a) = (term333 _144007 _144038 P P' f a).
Proof. exact (MK_COMB (@lem8134894) (@lem8134893 _144007 _144038 P P' p f a h1)). Qed.
Lemma lem8134901 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : p g a) : (p g a) = True.
Proof. exact (EQ_MP (@lem8134812 _144007 _144038 P p g a) (@lem8134809 _144007 _144038 P p g a h1)). Qed.
Lemma lem8134902 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134903 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : p g a) : (term333 _144007 _144038 P p g a) = (and True).
Proof. exact (MK_COMB (@lem8134902) (@lem8134901 _144007 _144038 P p g a h1)). Qed.
Lemma lem8134904 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (P' g a) = (P' g a).
Proof. exact (eq_refl (P' g a)). Qed.
Lemma lem8134905 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : p g a) : (term37 _144007 _144038 P p P' g a) = (term340 _144007 _144038 P P' g a).
Proof. exact (MK_COMB (@lem8134903 _144007 _144038 P p g a h1) (@lem8134904 _144007 _144038 P P' g a)). Qed.
Lemma lem8134907 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8134908 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term340 _144007 _144038 P P' g a) = (P' g a).
Proof. exact (@lem8134907 (P' g a)). Qed.
Lemma lem8134909 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : p g a) : (term37 _144007 _144038 P p P' g a) = (P' g a).
Proof. exact (TRANS (@lem8134905 _144007 _144038 P P' p g a h1) (@lem8134908 _144007 _144038 P P' g a)). Qed.
Lemma lem8134910 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134911 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : p g a) : (term42 _144007 _144038 P p P' g a) = (term333 _144007 _144038 P P' g a).
Proof. exact (MK_COMB (@lem8134910) (@lem8134909 _144007 _144038 P P' p g a h1)). Qed.
Lemma lem8134917 {_144006 _144007 _144038 P : Type'} (z : _144007) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) : (term332 _144006 _144007 _144038 P lt2 s a f g z) = True.
Proof. exact (EQ_MP (@lem8134817 _144006 _144007 _144038 P lt2 s a f g z) (@lem8134816 _144006 _144007 _144038 P z lt2 s a f g h1)). Qed.
Lemma lem8134918 {_144006 _144007 _144038 P : Type'} (z : _144007) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) : (term332 _144006 _144007 _144038 P lt2 s a f g z) = True.
Proof. exact (@lem8134917 _144006 _144007 _144038 P z lt2 s a f g h1). Qed.
Lemma lem8134919 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) : (term334 _144006 _144007 _144038 P lt2 s a f g) = (term335 _144007).
Proof. exact (fun_ext (fun z : _144007 => @lem8134918 _144006 _144007 _144038 P z lt2 s a f g h1)). Qed.
Lemma lem8134920 {_144007 : Type'} : (@all _144007) = (@all _144007).
Proof. exact (eq_refl (@all _144007)). Qed.
Lemma lem8134921 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) : (term43 _144006 _144007 _144038 P lt2 s a f g) = (term336 _144007).
Proof. exact (MK_COMB (@lem8134920 _144007) (@lem8134919 _144006 _144007 _144038 P lt2 s a f g h1)). Qed.
Lemma lem8134923 {A : Type'} (t : Prop) : (term337 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8134924 {_144007 : Type'} (t : Prop) : (term337 _144007 t) = t.
Proof. exact (@lem8134923 _144007 t). Qed.
Lemma lem8134925 {_144007 : Type'} : (term336 _144007) = True.
Proof. exact (@lem8134924 _144007 True). Qed.
Lemma lem8134926 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) : (term43 _144006 _144007 _144038 P lt2 s a f g) = True.
Proof. exact (TRANS (@lem8134921 _144006 _144007 _144038 P lt2 s a f g h1) (@lem8134925 _144007)). Qed.
Lemma lem8134927 {_144006 _144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : p g a) : (term45 _144006 _144007 _144038 P p P' lt2 s a f g) = (term341 _144007 _144038 P P' g a).
Proof. exact (MK_COMB (@lem8134911 _144007 _144038 P P' p g a h2) (@lem8134926 _144006 _144007 _144038 P lt2 s a f g h1)). Qed.
Lemma lem8134929 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem8134930 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term341 _144007 _144038 P P' g a) = (P' g a).
Proof. exact (@lem8134929 (P' g a)). Qed.
Lemma lem8134931 {_144006 _144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : p g a) : (term45 _144006 _144007 _144038 P p P' lt2 s a f g) = (P' g a).
Proof. exact (TRANS (@lem8134927 _144006 _144007 _144038 P P' lt2 s f p g a h1 h2) (@lem8134930 _144007 _144038 P P' g a)). Qed.
Lemma lem8134932 {_144006 _144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : p f a) (h3 : p g a) : (term47 _144006 _144007 _144038 P p P' lt2 s a f g) = (term342 _144007 _144038 P f P' g a).
Proof. exact (MK_COMB (@lem8134895 _144007 _144038 P P' p f a h2) (@lem8134931 _144006 _144007 _144038 P P' lt2 s f p g a h1 h3)). Qed.
Lemma lem8134935 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8134936 {_144006 _144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : p f a) (h3 : p g a) : (term49 _144006 _144007 _144038 P p P' lt2 s a f g) = (term343 _144007 _144038 P f P' g a).
Proof. exact (MK_COMB (@lem8134935) (@lem8134932 _144006 _144007 _144038 P P' lt2 s f p g a h1 h2 h3)). Qed.
Lemma lem8134939 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : ((h f a) = (h g a)) = ((h f a) = (h g a)).
Proof. exact (eq_refl ((h f a) = (h g a))). Qed.
Lemma lem8134940 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : p f a) (h3 : p g a) : (term51 _144006 _144007 _144038 _144063 P p P' lt2 s f h g a) = (term344 _144007 _144038 _144063 P P' f h g a).
Proof. exact (MK_COMB (@lem8134936 _144006 _144007 _144038 P P' lt2 s f p g a h1 h2 h3) (@lem8134939 _144007 _144038 _144063 P f h g a)). Qed.
Lemma lem8134943 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134944 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : p f a) (h3 : p g a) : (term154 _144006 _144007 _144038 _144063 P p P' lt2 s f h g a) = (term345 _144007 _144038 _144063 P P' f h g a).
Proof. exact (MK_COMB (@lem8134943) (@lem8134940 _144006 _144007 _144038 _144063 P P' h lt2 s f p g a h1 h2 h3)). Qed.
Lemma lem8134952 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : p f a) : (p f a) = True.
Proof. exact (EQ_MP (@lem8134810 _144007 _144038 P p f a) (@lem8134807 _144007 _144038 P p f a h1)). Qed.
Lemma lem8134953 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134954 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : p f a) : (term333 _144007 _144038 P p f a) = (and True).
Proof. exact (MK_COMB (@lem8134953) (@lem8134952 _144007 _144038 P p f a h1)). Qed.
Lemma lem8134955 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term346 _144007 _144038 P P' f a) = (term346 _144007 _144038 P P' f a).
Proof. exact (eq_refl (term346 _144007 _144038 P P' f a)). Qed.
Lemma lem8134956 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : p f a) : (term77 _144007 _144038 P p P' f a) = (term347 _144007 _144038 P P' f a).
Proof. exact (MK_COMB (@lem8134954 _144007 _144038 P p f a h1) (@lem8134955 _144007 _144038 P P' f a)). Qed.
Lemma lem8134958 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8134959 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term347 _144007 _144038 P P' f a) = (term346 _144007 _144038 P P' f a).
Proof. exact (@lem8134958 (term346 _144007 _144038 P P' f a)). Qed.
Lemma lem8134960 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : p f a) : (term77 _144007 _144038 P p P' f a) = (term346 _144007 _144038 P P' f a).
Proof. exact (TRANS (@lem8134956 _144007 _144038 P P' p f a h1) (@lem8134959 _144007 _144038 P P' f a)). Qed.
Lemma lem8134961 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134962 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : p f a) : (term82 _144007 _144038 P p P' f a) = (term348 _144007 _144038 P P' f a).
Proof. exact (MK_COMB (@lem8134961) (@lem8134960 _144007 _144038 P P' p f a h1)). Qed.
Lemma lem8134968 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : p g a) : (p g a) = True.
Proof. exact (EQ_MP (@lem8134812 _144007 _144038 P p g a) (@lem8134809 _144007 _144038 P p g a h1)). Qed.
Lemma lem8134969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134970 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : p g a) : (term333 _144007 _144038 P p g a) = (and True).
Proof. exact (MK_COMB (@lem8134969) (@lem8134968 _144007 _144038 P p g a h1)). Qed.
Lemma lem8134971 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term346 _144007 _144038 P P' g a) = (term346 _144007 _144038 P P' g a).
Proof. exact (eq_refl (term346 _144007 _144038 P P' g a)). Qed.
Lemma lem8134972 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : p g a) : (term77 _144007 _144038 P p P' g a) = (term347 _144007 _144038 P P' g a).
Proof. exact (MK_COMB (@lem8134970 _144007 _144038 P p g a h1) (@lem8134971 _144007 _144038 P P' g a)). Qed.
Lemma lem8134974 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8134975 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term347 _144007 _144038 P P' g a) = (term346 _144007 _144038 P P' g a).
Proof. exact (@lem8134974 (term346 _144007 _144038 P P' g a)). Qed.
Lemma lem8134976 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : p g a) : (term77 _144007 _144038 P p P' g a) = (term346 _144007 _144038 P P' g a).
Proof. exact (TRANS (@lem8134972 _144007 _144038 P P' p g a h1) (@lem8134975 _144007 _144038 P P' g a)). Qed.
Lemma lem8134977 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8134978 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : p g a) : (term82 _144007 _144038 P p P' g a) = (term348 _144007 _144038 P P' g a).
Proof. exact (MK_COMB (@lem8134977) (@lem8134976 _144007 _144038 P P' p g a h1)). Qed.
Lemma lem8134984 {_144006 _144007 _144038 P : Type'} (z : _144007) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) : (term332 _144006 _144007 _144038 P lt2 s a f g z) = True.
Proof. exact (EQ_MP (@lem8134817 _144006 _144007 _144038 P lt2 s a f g z) (@lem8134816 _144006 _144007 _144038 P z lt2 s a f g h1)). Qed.
Lemma lem8134985 {_144006 _144007 _144038 P : Type'} (z : _144007) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) : (term332 _144006 _144007 _144038 P lt2 s a f g z) = True.
Proof. exact (@lem8134984 _144006 _144007 _144038 P z lt2 s a f g h1). Qed.
Lemma lem8134986 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) : (term334 _144006 _144007 _144038 P lt2 s a f g) = (term335 _144007).
Proof. exact (fun_ext (fun z : _144007 => @lem8134985 _144006 _144007 _144038 P z lt2 s a f g h1)). Qed.
Lemma lem8134987 {_144007 : Type'} : (@all _144007) = (@all _144007).
Proof. exact (eq_refl (@all _144007)). Qed.
Lemma lem8134988 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) : (term43 _144006 _144007 _144038 P lt2 s a f g) = (term336 _144007).
Proof. exact (MK_COMB (@lem8134987 _144007) (@lem8134986 _144006 _144007 _144038 P lt2 s a f g h1)). Qed.
Lemma lem8134990 {A : Type'} (t : Prop) : (term337 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8134991 {_144007 : Type'} (t : Prop) : (term337 _144007 t) = t.
Proof. exact (@lem8134990 _144007 t). Qed.
Lemma lem8134992 {_144007 : Type'} : (term336 _144007) = True.
Proof. exact (@lem8134991 _144007 True). Qed.
Lemma lem8134993 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) : (term43 _144006 _144007 _144038 P lt2 s a f g) = True.
Proof. exact (TRANS (@lem8134988 _144006 _144007 _144038 P lt2 s a f g h1) (@lem8134992 _144007)). Qed.
Lemma lem8134994 {_144006 _144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : p g a) : (term84 _144006 _144007 _144038 P p P' lt2 s a f g) = (term349 _144007 _144038 P P' g a).
Proof. exact (MK_COMB (@lem8134978 _144007 _144038 P P' p g a h2) (@lem8134993 _144006 _144007 _144038 P lt2 s a f g h1)). Qed.
Lemma lem8134996 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem8134997 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term349 _144007 _144038 P P' g a) = (term346 _144007 _144038 P P' g a).
Proof. exact (@lem8134996 (term346 _144007 _144038 P P' g a)). Qed.
Lemma lem8134998 {_144006 _144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : p g a) : (term84 _144006 _144007 _144038 P p P' lt2 s a f g) = (term346 _144007 _144038 P P' g a).
Proof. exact (TRANS (@lem8134994 _144006 _144007 _144038 P P' lt2 s f p g a h1 h2) (@lem8134997 _144007 _144038 P P' g a)). Qed.
Lemma lem8134999 {_144006 _144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : p f a) (h3 : p g a) : (term86 _144006 _144007 _144038 P p P' lt2 s a f g) = (term350 _144007 _144038 P f P' g a).
Proof. exact (MK_COMB (@lem8134962 _144007 _144038 P P' p f a h2) (@lem8134998 _144006 _144007 _144038 P P' lt2 s f p g a h1 h3)). Qed.
Lemma lem8135002 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8135003 {_144006 _144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : p f a) (h3 : p g a) : (term88 _144006 _144007 _144038 P p P' lt2 s a f g) = (term351 _144007 _144038 P f P' g a).
Proof. exact (MK_COMB (@lem8135002) (@lem8134999 _144006 _144007 _144038 P P' lt2 s f p g a h1 h2 h3)). Qed.
Lemma lem8135006 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : ((k f a) = (k g a)) = ((k f a) = (k g a)).
Proof. exact (eq_refl ((k f a) = (k g a))). Qed.
Lemma lem8135007 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (k : type564 _144007 _144038 _144063 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : p f a) (h3 : p g a) : (term90 _144006 _144007 _144038 _144063 P p P' lt2 s f k g a) = (term352 _144007 _144038 _144063 P P' f k g a).
Proof. exact (MK_COMB (@lem8135003 _144006 _144007 _144038 P P' lt2 s f p g a h1 h2 h3) (@lem8135006 _144007 _144038 _144063 P f k g a)). Qed.
Lemma lem8135010 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (k : type564 _144007 _144038 _144063 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : p f a) (h3 : p g a) : (term156 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a) = (term353 _144007 _144038 _144063 P h P' f k g a).
Proof. exact (MK_COMB (@lem8134944 _144006 _144007 _144038 _144063 P P' h lt2 s f p g a h1 h2 h3) (@lem8135007 _144006 _144007 _144038 _144063 P P' k lt2 s f p g a h1 h2 h3)). Qed.
Lemma lem8135013 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (k : type564 _144007 _144038 _144063 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : p f a) (h3 : p g a) : (term222 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a) = (term354 _144007 _144038 _144063 P h P' f k g a).
Proof. exact (MK_COMB (@lem8134875 _144006 _144007 _144038 P P' lt2 s f p g a h1 h2 h3) (@lem8135010 _144006 _144007 _144038 _144063 P h P' k lt2 s f p g a h1 h2 h3)). Qed.
Lemma lem8135016 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8135017 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (k : type564 _144007 _144038 _144063 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : p f a) (h3 : p g a) : (term312 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a) = (term355 _144007 _144038 _144063 P h P' f k g a).
Proof. exact (MK_COMB (@lem8135016) (@lem8135013 _144006 _144007 _144038 _144063 P h P' k lt2 s f p g a h1 h2 h3)). Qed.
Lemma lem8135020 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : ((term246 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k g a)) = ((term246 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k g a)).
Proof. exact (eq_refl ((term246 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k g a))). Qed.
Lemma lem8135021 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : p f a) (h3 : p g a) : (term356 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a) = (term357 _144007 _144038 _144063 P f P' h k g a).
Proof. exact (MK_COMB (@lem8135017 _144006 _144007 _144038 _144063 P h P' k lt2 s f p g a h1 h2 h3) (@lem8135020 _144007 _144038 _144063 P f P' h k g a)). Qed.
Lemma lem8135024 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : p f a) (h3 : p g a) : (term357 _144007 _144038 _144063 P f P' h k g a) = (term356 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a).
Proof. exact (SYM (@lem8135021 _144006 _144007 _144038 _144063 P P' h k lt2 s f p g a h1 h2 h3)). Qed.
Lemma lem8135026 (p : Prop) : p = (term358 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8135027 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term357 _144007 _144038 _144063 P f P' h k g a) = (term359 _144007 _144038 _144063 P f P' h k g a).
Proof. exact (@lem8135026 (term357 _144007 _144038 _144063 P f P' h k g a)). Qed.
Lemma lem8135028 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term359 _144007 _144038 _144063 P f P' h k g a) = (term357 _144007 _144038 _144063 P f P' h k g a).
Proof. exact (SYM (@lem8135027 _144007 _144038 _144063 P f P' h k g a)). Qed.
Lemma lem8135029 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) (h1 : term360 _144007 _144038 _144063 P f P' h k g a) : term360 _144007 _144038 _144063 P f P' h k g a.
Proof. exact (h1). Qed.
Lemma lem8135032 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) (h1 : term361 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a) : term361 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a.
Proof. exact (h1). Qed.
Lemma lem8135033 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : term362 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a.
Proof. exact (fun h0 : term361 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a => @lem8135032 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a h0). Qed.
Lemma lem8135034 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) (h1 : term362 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a) : term362 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a.
Proof. exact (h1). Qed.
Lemma lem8135035 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) (h1 : term361 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a) : term361 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a.
Proof. exact (h1). Qed.
Lemma lem8135036 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) (h1 : term362 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a) (h2 : term361 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a) : term361 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a.
Proof. exact (@lem8135034 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a h1 (@lem8135035 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a h2)). Qed.
Lemma lem8135037 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) (h1 : term361 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a) : term363 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a.
Proof. exact (fun h0 : term362 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a => @lem8135036 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a h0 h1). Qed.
Lemma lem8135038 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) (h1 : term362 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a) : term362 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a.
Proof. exact (h1). Qed.
Lemma lem8135039 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) (h1 : term362 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a) (h2 : term361 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a) : term361 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a.
Proof. exact (@lem8135037 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a h2 (@lem8135038 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a h1)). Qed.
Lemma lem8135040 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) (h1 : term362 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a) : term362 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a.
Proof. exact (fun h0 : term361 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a => @lem8135039 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a h1 h0). Qed.
Lemma lem8135041 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : term364 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a.
Proof. exact (fun h0 : term362 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a => @lem8135040 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a h0). Qed.
Lemma lem8135044 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : term362 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a.
Proof. exact (@lem8135041 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a (@lem8135033 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a)). Qed.
Lemma lem8135045 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : term362 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a.
Proof. exact (@lem8135044 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a). Qed.
Lemma lem8135095 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem8135096 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term359 _144007 _144038 _144063 P f P' h k g a) = (term365 _144007 _144038 _144063 P f P' h k g a).
Proof. exact (@lem8135095 (term360 _144007 _144038 _144063 P f P' h k g a)). Qed.
Lemma lem8135098 (t : Prop) : (term366 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem8135099 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term365 _144007 _144038 _144063 P f P' h k g a) = (term357 _144007 _144038 _144063 P f P' h k g a).
Proof. exact (@lem8135098 (term357 _144007 _144038 _144063 P f P' h k g a)). Qed.
Lemma lem8135102 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term359 _144007 _144038 _144063 P f P' h k g a) = (term357 _144007 _144038 _144063 P f P' h k g a).
Proof. exact (TRANS (@lem8135096 _144007 _144038 _144063 P f P' h k g a) (@lem8135099 _144007 _144038 _144063 P f P' h k g a)). Qed.
Lemma lem8135115 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) : (term367 _144006 _144007 _144038 P lt2 s a f g) = (term367 _144006 _144007 _144038 P lt2 s a f g).
Proof. exact (eq_refl (term367 _144006 _144007 _144038 P lt2 s a f g)). Qed.
Lemma lem8135116 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term368 _144006 _144007 _144038 _144063 P lt2 s f P' h k g a) = (term369 _144006 _144007 _144038 _144063 P lt2 s f P' h k g a).
Proof. exact (MK_COMB (@lem8135115 _144006 _144007 _144038 P lt2 s a f g) (@lem8135102 _144007 _144038 _144063 P f P' h k g a)). Qed.
Lemma lem8135119 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term370 _144007 _144038 P p g a) = (term370 _144007 _144038 P p g a).
Proof. exact (eq_refl (term370 _144007 _144038 P p g a)). Qed.
Lemma lem8135120 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term371 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a) = (term372 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a).
Proof. exact (MK_COMB (@lem8135119 _144007 _144038 P p g a) (@lem8135116 _144006 _144007 _144038 _144063 P lt2 s f P' h k g a)). Qed.
Lemma lem8135123 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term370 _144007 _144038 P p f a) = (term370 _144007 _144038 P p f a).
Proof. exact (eq_refl (term370 _144007 _144038 P p f a)). Qed.
Lemma lem8135124 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term361 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a) = (term373 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a).
Proof. exact (MK_COMB (@lem8135123 _144007 _144038 P p f a) (@lem8135120 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a)). Qed.
Lemma lem8135127 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term374 _144006 _144007 _144038 _144063 P lt2 s f P' h k g a) = (term375 _144006 _144007 _144038 _144063 P lt2 s f P' h k g a).
Proof. exact (fun_ext (fun p : type560 _144007 _144038 P => @lem8135124 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a)). Qed.
Lemma lem8135128 {_144007 _144038 P : Type'} : (@all ((_144007 -> _144038) -> P -> Prop)) = (@all ((_144007 -> _144038) -> P -> Prop)).
Proof. exact (eq_refl (@all ((_144007 -> _144038) -> P -> Prop))). Qed.
Lemma lem8135129 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term376 _144006 _144007 _144038 _144063 P lt2 s f P' h k g a) = (term377 _144006 _144007 _144038 _144063 P lt2 s f P' h k g a).
Proof. exact (MK_COMB (@lem8135128 _144007 _144038 P) (@lem8135127 _144006 _144007 _144038 _144063 P lt2 s f P' h k g a)). Qed.
Lemma lem8135134 {_144006 _144007 _144038 _144063 P : Type'} (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term378 _144006 _144007 _144038 _144063 P s f P' h k g a) = (term379 _144006 _144007 _144038 _144063 P s f P' h k g a).
Proof. exact (fun_ext (fun lt2 : type1470 _144006 _144007 => @lem8135129 _144006 _144007 _144038 _144063 P lt2 s f P' h k g a)). Qed.
Lemma lem8135135 {_144006 _144007 : Type'} : (@all (_144007 -> _144006 -> Prop)) = (@all (_144007 -> _144006 -> Prop)).
Proof. exact (eq_refl (@all (_144007 -> _144006 -> Prop))). Qed.
Lemma lem8135136 {_144006 _144007 _144038 _144063 P : Type'} (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term380 _144006 _144007 _144038 _144063 P s f P' h k g a) = (term381 _144006 _144007 _144038 _144063 P s f P' h k g a).
Proof. exact (MK_COMB (@lem8135135 _144006 _144007) (@lem8135134 _144006 _144007 _144038 _144063 P s f P' h k g a)). Qed.
Lemma lem8135141 {_144006 _144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term382 _144006 _144007 _144038 _144063 P f P' h k g a) = (term383 _144006 _144007 _144038 _144063 P f P' h k g a).
Proof. exact (fun_ext (fun s : P -> _144006 => @lem8135136 _144006 _144007 _144038 _144063 P s f P' h k g a)). Qed.
Lemma lem8135142 {_144006 P : Type'} : (@all (P -> _144006)) = (@all (P -> _144006)).
Proof. exact (eq_refl (@all (P -> _144006))). Qed.
Lemma lem8135143 {_144006 _144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term384 _144006 _144007 _144038 _144063 P f P' h k g a) = (term385 _144006 _144007 _144038 _144063 P f P' h k g a).
Proof. exact (MK_COMB (@lem8135142 _144006 P) (@lem8135141 _144006 _144007 _144038 _144063 P f P' h k g a)). Qed.
Lemma lem8135148 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term386 _144006 _144007 _144038 _144063 P P' h k g a) = (term387 _144006 _144007 _144038 _144063 P P' h k g a).
Proof. exact (fun_ext (fun f : _144007 -> _144038 => @lem8135143 _144006 _144007 _144038 _144063 P f P' h k g a)). Qed.
Lemma lem8135149 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8135150 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term388 _144006 _144007 _144038 _144063 P P' h k g a) = (term389 _144006 _144007 _144038 _144063 P P' h k g a).
Proof. exact (MK_COMB (@lem8135149 _144007 _144038) (@lem8135148 _144006 _144007 _144038 _144063 P P' h k g a)). Qed.
Lemma lem8135155 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term390 _144006 _144007 _144038 _144063 P h k g a) = (term391 _144006 _144007 _144038 _144063 P h k g a).
Proof. exact (fun_ext (fun P' : type560 _144007 _144038 P => @lem8135150 _144006 _144007 _144038 _144063 P P' h k g a)). Qed.
Lemma lem8135156 {_144007 _144038 P : Type'} : (@all ((_144007 -> _144038) -> P -> Prop)) = (@all ((_144007 -> _144038) -> P -> Prop)).
Proof. exact (eq_refl (@all ((_144007 -> _144038) -> P -> Prop))). Qed.
Lemma lem8135157 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term392 _144006 _144007 _144038 _144063 P h k g a) = (term393 _144006 _144007 _144038 _144063 P h k g a).
Proof. exact (MK_COMB (@lem8135156 _144007 _144038 P) (@lem8135155 _144006 _144007 _144038 _144063 P h k g a)). Qed.
Lemma lem8135162 {_144006 _144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term394 _144006 _144007 _144038 _144063 P k g a) = (term395 _144006 _144007 _144038 _144063 P k g a).
Proof. exact (fun_ext (fun h : type564 _144007 _144038 _144063 P => @lem8135157 _144006 _144007 _144038 _144063 P h k g a)). Qed.
Lemma lem8135163 {_144007 _144038 _144063 P : Type'} : (@all ((_144007 -> _144038) -> P -> _144063)) = (@all ((_144007 -> _144038) -> P -> _144063)).
Proof. exact (eq_refl (@all ((_144007 -> _144038) -> P -> _144063))). Qed.
Lemma lem8135164 {_144006 _144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term396 _144006 _144007 _144038 _144063 P k g a) = (term397 _144006 _144007 _144038 _144063 P k g a).
Proof. exact (MK_COMB (@lem8135163 _144007 _144038 _144063 P) (@lem8135162 _144006 _144007 _144038 _144063 P k g a)). Qed.
Lemma lem8135169 {_144006 _144007 _144038 _144063 P : Type'} (g : _144007 -> _144038) (a : P) : (term398 _144006 _144007 _144038 _144063 P g a) = (term399 _144006 _144007 _144038 _144063 P g a).
Proof. exact (fun_ext (fun k : type564 _144007 _144038 _144063 P => @lem8135164 _144006 _144007 _144038 _144063 P k g a)). Qed.
Lemma lem8135170 {_144007 _144038 _144063 P : Type'} : (@all ((_144007 -> _144038) -> P -> _144063)) = (@all ((_144007 -> _144038) -> P -> _144063)).
Proof. exact (eq_refl (@all ((_144007 -> _144038) -> P -> _144063))). Qed.
Lemma lem8135171 {_144006 _144007 _144038 _144063 P : Type'} (g : _144007 -> _144038) (a : P) : (term400 _144006 _144007 _144038 _144063 P g a) = (term401 _144006 _144007 _144038 _144063 P g a).
Proof. exact (MK_COMB (@lem8135170 _144007 _144038 _144063 P) (@lem8135169 _144006 _144007 _144038 _144063 P g a)). Qed.
Lemma lem8135176 {_144006 _144007 _144038 _144063 P : Type'} (a : P) : (term402 _144006 _144007 _144038 _144063 P a) = (term403 _144006 _144007 _144038 _144063 P a).
Proof. exact (fun_ext (fun g : _144007 -> _144038 => @lem8135171 _144006 _144007 _144038 _144063 P g a)). Qed.
Lemma lem8135177 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8135178 {_144006 _144007 _144038 _144063 P : Type'} (a : P) : (term404 _144006 _144007 _144038 _144063 P a) = (term405 _144006 _144007 _144038 _144063 P a).
Proof. exact (MK_COMB (@lem8135177 _144007 _144038) (@lem8135176 _144006 _144007 _144038 _144063 P a)). Qed.
Lemma lem8135183 {_144006 _144007 _144038 _144063 P : Type'} : (term406 _144006 _144007 _144038 _144063 P) = (term407 _144006 _144007 _144038 _144063 P).
Proof. exact (fun_ext (fun a : P => @lem8135178 _144006 _144007 _144038 _144063 P a)). Qed.
Lemma lem8135184 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8135193 {_144006 _144007 _144038 _144063 P : Type'} : (term408 _144006 _144007 _144038 _144063 P) = (term409 _144006 _144007 _144038 _144063 P).
Proof. exact (MK_COMB (@lem8135184 P) (@lem8135183 _144006 _144007 _144038 _144063 P)). Qed.
Lemma lem8135205 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (P' g a) = False.
Proof. exact (h1). Qed.
Lemma lem8135206 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term410 _144007 _144038 P P' f a) = (term410 _144007 _144038 P P' f a).
Proof. exact (eq_refl (term410 _144007 _144038 P P' f a)). Qed.
Lemma lem8135207 {_144007 _144038 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : ((P' f a) = (P' g a)) = ((P' f a) = False).
Proof. exact (MK_COMB (@lem8135206 _144007 _144038 P P' f a) (@lem8135205 _144007 _144038 P P' g a h1)). Qed.
Lemma lem8135209 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem8135210 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : ((P' f a) = False) = (term346 _144007 _144038 P P' f a).
Proof. exact (@lem8135209 (P' f a)). Qed.
Lemma lem8135211 {_144007 _144038 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : ((P' f a) = (P' g a)) = (term346 _144007 _144038 P P' f a).
Proof. exact (TRANS (@lem8135207 _144007 _144038 P f P' g a h1) (@lem8135210 _144007 _144038 P P' f a)). Qed.
Lemma lem8135212 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8135213 {_144007 _144038 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term339 _144007 _144038 P f P' g a) = (term348 _144007 _144038 P P' f a).
Proof. exact (MK_COMB (@lem8135212) (@lem8135211 _144007 _144038 P f P' g a h1)). Qed.
Lemma lem8135215 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (P' g a) = False.
Proof. exact (h1). Qed.
Lemma lem8135216 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term333 _144007 _144038 P P' f a) = (term333 _144007 _144038 P P' f a).
Proof. exact (eq_refl (term333 _144007 _144038 P P' f a)). Qed.
Lemma lem8135217 {_144007 _144038 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term342 _144007 _144038 P f P' g a) = (term411 _144007 _144038 P P' f a).
Proof. exact (MK_COMB (@lem8135216 _144007 _144038 P P' f a) (@lem8135215 _144007 _144038 P P' g a h1)). Qed.
Lemma lem8135219 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem8135220 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term411 _144007 _144038 P P' f a) = False.
Proof. exact (@lem8135219 (P' f a)). Qed.
Lemma lem8135221 {_144007 _144038 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term342 _144007 _144038 P f P' g a) = False.
Proof. exact (TRANS (@lem8135217 _144007 _144038 P f P' g a h1) (@lem8135220 _144007 _144038 P P' f a)). Qed.
Lemma lem8135222 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8135223 {_144007 _144038 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term343 _144007 _144038 P f P' g a) = (imp False).
Proof. exact (MK_COMB (@lem8135222) (@lem8135221 _144007 _144038 P f P' g a h1)). Qed.
Lemma lem8135226 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : ((h f a) = (h g a)) = ((h f a) = (h g a)).
Proof. exact (eq_refl ((h f a) = (h g a))). Qed.
Lemma lem8135227 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term344 _144007 _144038 _144063 P P' f h g a) = (term412 _144007 _144038 _144063 P f h g a).
Proof. exact (MK_COMB (@lem8135223 _144007 _144038 P f P' g a h1) (@lem8135226 _144007 _144038 _144063 P f h g a)). Qed.
Lemma lem8135229 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem8135230 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term412 _144007 _144038 _144063 P f h g a) = True.
Proof. exact (@lem8135229 ((h f a) = (h g a))). Qed.
Lemma lem8135231 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term344 _144007 _144038 _144063 P P' f h g a) = True.
Proof. exact (TRANS (@lem8135227 _144007 _144038 _144063 P f h P' g a h1) (@lem8135230 _144007 _144038 _144063 P f h g a)). Qed.
Lemma lem8135232 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8135233 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term345 _144007 _144038 _144063 P P' f h g a) = (and True).
Proof. exact (MK_COMB (@lem8135232) (@lem8135231 _144007 _144038 _144063 P f h P' g a h1)). Qed.
Lemma lem8135235 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (P' g a) = False.
Proof. exact (h1). Qed.
Lemma lem8135236 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8135237 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term346 _144007 _144038 P P' g a) = (~ False).
Proof. exact (MK_COMB (@lem8135236) (@lem8135235 _144007 _144038 P P' g a h1)). Qed.
Lemma lem8135239 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem8135240 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term346 _144007 _144038 P P' g a) = True.
Proof. exact (TRANS (@lem8135237 _144007 _144038 P P' g a h1) (@lem8135239)). Qed.
Lemma lem8135241 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term348 _144007 _144038 P P' f a) = (term348 _144007 _144038 P P' f a).
Proof. exact (eq_refl (term348 _144007 _144038 P P' f a)). Qed.
Lemma lem8135242 {_144007 _144038 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term350 _144007 _144038 P f P' g a) = (term349 _144007 _144038 P P' f a).
Proof. exact (MK_COMB (@lem8135241 _144007 _144038 P P' f a) (@lem8135240 _144007 _144038 P P' g a h1)). Qed.
Lemma lem8135244 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem8135245 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term349 _144007 _144038 P P' f a) = (term346 _144007 _144038 P P' f a).
Proof. exact (@lem8135244 (term346 _144007 _144038 P P' f a)). Qed.
Lemma lem8135246 {_144007 _144038 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term350 _144007 _144038 P f P' g a) = (term346 _144007 _144038 P P' f a).
Proof. exact (TRANS (@lem8135242 _144007 _144038 P f P' g a h1) (@lem8135245 _144007 _144038 P P' f a)). Qed.
Lemma lem8135247 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8135248 {_144007 _144038 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term351 _144007 _144038 P f P' g a) = (term413 _144007 _144038 P P' f a).
Proof. exact (MK_COMB (@lem8135247) (@lem8135246 _144007 _144038 P f P' g a h1)). Qed.
Lemma lem8135251 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : ((k f a) = (k g a)) = ((k f a) = (k g a)).
Proof. exact (eq_refl ((k f a) = (k g a))). Qed.
Lemma lem8135252 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term352 _144007 _144038 _144063 P P' f k g a) = (term414 _144007 _144038 _144063 P P' f k g a).
Proof. exact (MK_COMB (@lem8135248 _144007 _144038 P f P' g a h1) (@lem8135251 _144007 _144038 _144063 P f k g a)). Qed.
Lemma lem8135255 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term353 _144007 _144038 _144063 P h P' f k g a) = (term415 _144007 _144038 _144063 P P' f k g a).
Proof. exact (MK_COMB (@lem8135233 _144007 _144038 _144063 P f h P' g a h1) (@lem8135252 _144007 _144038 _144063 P f k P' g a h1)). Qed.
Lemma lem8135257 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8135258 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term415 _144007 _144038 _144063 P P' f k g a) = (term414 _144007 _144038 _144063 P P' f k g a).
Proof. exact (@lem8135257 (term414 _144007 _144038 _144063 P P' f k g a)). Qed.
Lemma lem8135261 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term353 _144007 _144038 _144063 P h P' f k g a) = (term414 _144007 _144038 _144063 P P' f k g a).
Proof. exact (TRANS (@lem8135255 _144007 _144038 _144063 P h f k P' g a h1) (@lem8135258 _144007 _144038 _144063 P P' f k g a)). Qed.
Lemma lem8135262 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term354 _144007 _144038 _144063 P h P' f k g a) = (term416 _144007 _144038 _144063 P P' f k g a).
Proof. exact (MK_COMB (@lem8135213 _144007 _144038 P f P' g a h1) (@lem8135261 _144007 _144038 _144063 P h f k P' g a h1)). Qed.
Lemma lem8135265 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8135266 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term355 _144007 _144038 _144063 P h P' f k g a) = (term417 _144007 _144038 _144063 P P' f k g a).
Proof. exact (MK_COMB (@lem8135265) (@lem8135262 _144007 _144038 _144063 P h f k P' g a h1)). Qed.
Lemma lem8135268 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (P' g a) = False.
Proof. exact (h1). Qed.
Lemma lem8135269 {_144063 : Type'} : (@COND _144063) = (@COND _144063).
Proof. exact (eq_refl (@COND _144063)). Qed.
Lemma lem8135270 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term418 _144007 _144038 _144063 P P' g a) = (@COND _144063 False).
Proof. exact (MK_COMB (@lem8135269 _144063) (@lem8135268 _144007 _144038 P P' g a h1)). Qed.
Lemma lem8135271 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (h g a) = (h g a).
Proof. exact (eq_refl (h g a)). Qed.
Lemma lem8135272 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term419 _144007 _144038 _144063 P P' h g a) = (term420 _144007 _144038 _144063 P h g a).
Proof. exact (MK_COMB (@lem8135270 _144007 _144038 _144063 P P' g a h1) (@lem8135271 _144007 _144038 _144063 P h g a)). Qed.
Lemma lem8135273 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (k g a) = (k g a).
Proof. exact (eq_refl (k g a)). Qed.
Lemma lem8135274 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term246 _144007 _144038 _144063 P P' h k g a) = (term421 _144007 _144038 _144063 P h k g a).
Proof. exact (MK_COMB (@lem8135272 _144007 _144038 _144063 P h P' g a h1) (@lem8135273 _144007 _144038 _144063 P k g a)). Qed.
Lemma lem8135276 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8135277 {_144063 : Type'} (t1 : _144063) (t2 : _144063) : (@COND _144063 False t1 t2) = t2.
Proof. exact (@lem8135276 _144063 t1 t2). Qed.
Lemma lem8135278 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term421 _144007 _144038 _144063 P h k g a) = (k g a).
Proof. exact (@lem8135277 _144063 (h g a) (k g a)). Qed.
Lemma lem8135279 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term246 _144007 _144038 _144063 P P' h k g a) = (k g a).
Proof. exact (TRANS (@lem8135274 _144007 _144038 _144063 P h k P' g a h1) (@lem8135278 _144007 _144038 _144063 P h k g a)). Qed.
Lemma lem8135280 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (a : P) : (term251 _144007 _144038 _144063 P P' h k f a) = (term251 _144007 _144038 _144063 P P' h k f a).
Proof. exact (eq_refl (term251 _144007 _144038 _144063 P P' h k f a)). Qed.
Lemma lem8135281 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : ((term246 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k g a)) = ((term246 _144007 _144038 _144063 P P' h k f a) = (k g a)).
Proof. exact (MK_COMB (@lem8135280 _144007 _144038 _144063 P P' h k f a) (@lem8135279 _144007 _144038 _144063 P h k P' g a h1)). Qed.
Lemma lem8135284 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term357 _144007 _144038 _144063 P f P' h k g a) = (term422 _144007 _144038 _144063 P P' h f k g a).
Proof. exact (MK_COMB (@lem8135266 _144007 _144038 _144063 P h f k P' g a h1) (@lem8135281 _144007 _144038 _144063 P h f k P' g a h1)). Qed.
Lemma lem8135287 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) : (term367 _144006 _144007 _144038 P lt2 s a f g) = (term367 _144006 _144007 _144038 P lt2 s a f g).
Proof. exact (eq_refl (term367 _144006 _144007 _144038 P lt2 s a f g)). Qed.
Lemma lem8135288 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term369 _144006 _144007 _144038 _144063 P lt2 s f P' h k g a) = (term423 _144006 _144007 _144038 _144063 P lt2 s P' h f k g a).
Proof. exact (MK_COMB (@lem8135287 _144006 _144007 _144038 P lt2 s a f g) (@lem8135284 _144007 _144038 _144063 P h f k P' g a h1)). Qed.
Lemma lem8135291 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term370 _144007 _144038 P p g a) = (term370 _144007 _144038 P p g a).
Proof. exact (eq_refl (term370 _144007 _144038 P p g a)). Qed.
Lemma lem8135292 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term372 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a) = (term424 _144006 _144007 _144038 _144063 P p lt2 s P' h f k g a).
Proof. exact (MK_COMB (@lem8135291 _144007 _144038 P p g a) (@lem8135288 _144006 _144007 _144038 _144063 P lt2 s h f k P' g a h1)). Qed.
Lemma lem8135295 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term370 _144007 _144038 P p f a) = (term370 _144007 _144038 P p f a).
Proof. exact (eq_refl (term370 _144007 _144038 P p f a)). Qed.
Lemma lem8135296 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term373 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a) = (term425 _144006 _144007 _144038 _144063 P p lt2 s P' h f k g a).
Proof. exact (MK_COMB (@lem8135295 _144007 _144038 P p f a) (@lem8135292 _144006 _144007 _144038 _144063 P p lt2 s h f k P' g a h1)). Qed.
Lemma lem8135299 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term375 _144006 _144007 _144038 _144063 P lt2 s f P' h k g a) = (term426 _144006 _144007 _144038 _144063 P lt2 s P' h f k g a).
Proof. exact (fun_ext (fun p : type560 _144007 _144038 P => @lem8135296 _144006 _144007 _144038 _144063 P p lt2 s h f k P' g a h1)). Qed.
Lemma lem8135300 {_144007 _144038 P : Type'} : (@all ((_144007 -> _144038) -> P -> Prop)) = (@all ((_144007 -> _144038) -> P -> Prop)).
Proof. exact (eq_refl (@all ((_144007 -> _144038) -> P -> Prop))). Qed.
Lemma lem8135301 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term377 _144006 _144007 _144038 _144063 P lt2 s f P' h k g a) = (term427 _144006 _144007 _144038 _144063 P lt2 s P' h f k g a).
Proof. exact (MK_COMB (@lem8135300 _144007 _144038 P) (@lem8135299 _144006 _144007 _144038 _144063 P lt2 s h f k P' g a h1)). Qed.
Lemma lem8135306 {_144006 _144007 _144038 _144063 P : Type'} (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term379 _144006 _144007 _144038 _144063 P s f P' h k g a) = (term428 _144006 _144007 _144038 _144063 P s P' h f k g a).
Proof. exact (fun_ext (fun lt2 : type1470 _144006 _144007 => @lem8135301 _144006 _144007 _144038 _144063 P lt2 s h f k P' g a h1)). Qed.
Lemma lem8135307 {_144006 _144007 : Type'} : (@all (_144007 -> _144006 -> Prop)) = (@all (_144007 -> _144006 -> Prop)).
Proof. exact (eq_refl (@all (_144007 -> _144006 -> Prop))). Qed.
Lemma lem8135308 {_144006 _144007 _144038 _144063 P : Type'} (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term381 _144006 _144007 _144038 _144063 P s f P' h k g a) = (term429 _144006 _144007 _144038 _144063 P s P' h f k g a).
Proof. exact (MK_COMB (@lem8135307 _144006 _144007) (@lem8135306 _144006 _144007 _144038 _144063 P s h f k P' g a h1)). Qed.
Lemma lem8135313 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term383 _144006 _144007 _144038 _144063 P f P' h k g a) = (term430 _144006 _144007 _144038 _144063 P P' h f k g a).
Proof. exact (fun_ext (fun s : P -> _144006 => @lem8135308 _144006 _144007 _144038 _144063 P s h f k P' g a h1)). Qed.
Lemma lem8135314 {_144006 P : Type'} : (@all (P -> _144006)) = (@all (P -> _144006)).
Proof. exact (eq_refl (@all (P -> _144006))). Qed.
Lemma lem8135315 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term385 _144006 _144007 _144038 _144063 P f P' h k g a) = (term431 _144006 _144007 _144038 _144063 P P' h f k g a).
Proof. exact (MK_COMB (@lem8135314 _144006 P) (@lem8135313 _144006 _144007 _144038 _144063 P h f k P' g a h1)). Qed.
Lemma lem8135320 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term387 _144006 _144007 _144038 _144063 P P' h k g a) = (term432 _144006 _144007 _144038 _144063 P P' h k g a).
Proof. exact (fun_ext (fun f : _144007 -> _144038 => @lem8135315 _144006 _144007 _144038 _144063 P h f k P' g a h1)). Qed.
Lemma lem8135321 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8135322 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = False) : (term389 _144006 _144007 _144038 _144063 P P' h k g a) = (term433 _144006 _144007 _144038 _144063 P P' h k g a).
Proof. exact (MK_COMB (@lem8135321 _144007 _144038) (@lem8135320 _144006 _144007 _144038 _144063 P h k P' g a h1)). Qed.
Lemma lem8135327 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : term434 _144006 _144007 _144038 _144063 P P' h k g a.
Proof. exact (fun h0 : (P' g a) = False => @lem8135322 _144006 _144007 _144038 _144063 P h k P' g a h0). Qed.
Lemma lem8135337 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (P' g a) = True.
Proof. exact (h1). Qed.
Lemma lem8135338 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term410 _144007 _144038 P P' f a) = (term410 _144007 _144038 P P' f a).
Proof. exact (eq_refl (term410 _144007 _144038 P P' f a)). Qed.
Lemma lem8135339 {_144007 _144038 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : ((P' f a) = (P' g a)) = ((P' f a) = True).
Proof. exact (MK_COMB (@lem8135338 _144007 _144038 P P' f a) (@lem8135337 _144007 _144038 P P' g a h1)). Qed.
Lemma lem8135341 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem8135342 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : ((P' f a) = True) = (P' f a).
Proof. exact (@lem8135341 (P' f a)). Qed.
Lemma lem8135343 {_144007 _144038 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : ((P' f a) = (P' g a)) = (P' f a).
Proof. exact (TRANS (@lem8135339 _144007 _144038 P f P' g a h1) (@lem8135342 _144007 _144038 P P' f a)). Qed.
Lemma lem8135344 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8135345 {_144007 _144038 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term339 _144007 _144038 P f P' g a) = (term333 _144007 _144038 P P' f a).
Proof. exact (MK_COMB (@lem8135344) (@lem8135343 _144007 _144038 P f P' g a h1)). Qed.
Lemma lem8135347 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (P' g a) = True.
Proof. exact (h1). Qed.
Lemma lem8135348 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term333 _144007 _144038 P P' f a) = (term333 _144007 _144038 P P' f a).
Proof. exact (eq_refl (term333 _144007 _144038 P P' f a)). Qed.
Lemma lem8135349 {_144007 _144038 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term342 _144007 _144038 P f P' g a) = (term341 _144007 _144038 P P' f a).
Proof. exact (MK_COMB (@lem8135348 _144007 _144038 P P' f a) (@lem8135347 _144007 _144038 P P' g a h1)). Qed.
Lemma lem8135351 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem8135352 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term341 _144007 _144038 P P' f a) = (P' f a).
Proof. exact (@lem8135351 (P' f a)). Qed.
Lemma lem8135353 {_144007 _144038 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term342 _144007 _144038 P f P' g a) = (P' f a).
Proof. exact (TRANS (@lem8135349 _144007 _144038 P f P' g a h1) (@lem8135352 _144007 _144038 P P' f a)). Qed.
Lemma lem8135354 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8135355 {_144007 _144038 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term343 _144007 _144038 P f P' g a) = (term370 _144007 _144038 P P' f a).
Proof. exact (MK_COMB (@lem8135354) (@lem8135353 _144007 _144038 P f P' g a h1)). Qed.
Lemma lem8135358 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : ((h f a) = (h g a)) = ((h f a) = (h g a)).
Proof. exact (eq_refl ((h f a) = (h g a))). Qed.
Lemma lem8135359 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term344 _144007 _144038 _144063 P P' f h g a) = (term435 _144007 _144038 _144063 P P' f h g a).
Proof. exact (MK_COMB (@lem8135355 _144007 _144038 P f P' g a h1) (@lem8135358 _144007 _144038 _144063 P f h g a)). Qed.
Lemma lem8135362 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8135363 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term345 _144007 _144038 _144063 P P' f h g a) = (term436 _144007 _144038 _144063 P P' f h g a).
Proof. exact (MK_COMB (@lem8135362) (@lem8135359 _144007 _144038 _144063 P f h P' g a h1)). Qed.
Lemma lem8135365 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (P' g a) = True.
Proof. exact (h1). Qed.
Lemma lem8135366 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8135367 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term346 _144007 _144038 P P' g a) = (~ True).
Proof. exact (MK_COMB (@lem8135366) (@lem8135365 _144007 _144038 P P' g a h1)). Qed.
Lemma lem8135369 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem8135370 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term346 _144007 _144038 P P' g a) = False.
Proof. exact (TRANS (@lem8135367 _144007 _144038 P P' g a h1) (@lem8135369)). Qed.
Lemma lem8135371 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term348 _144007 _144038 P P' f a) = (term348 _144007 _144038 P P' f a).
Proof. exact (eq_refl (term348 _144007 _144038 P P' f a)). Qed.
Lemma lem8135372 {_144007 _144038 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term350 _144007 _144038 P f P' g a) = (term437 _144007 _144038 P P' f a).
Proof. exact (MK_COMB (@lem8135371 _144007 _144038 P P' f a) (@lem8135370 _144007 _144038 P P' g a h1)). Qed.
Lemma lem8135374 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem8135375 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term437 _144007 _144038 P P' f a) = False.
Proof. exact (@lem8135374 (term346 _144007 _144038 P P' f a)). Qed.
Lemma lem8135376 {_144007 _144038 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term350 _144007 _144038 P f P' g a) = False.
Proof. exact (TRANS (@lem8135372 _144007 _144038 P f P' g a h1) (@lem8135375 _144007 _144038 P P' f a)). Qed.
Lemma lem8135377 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8135378 {_144007 _144038 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term351 _144007 _144038 P f P' g a) = (imp False).
Proof. exact (MK_COMB (@lem8135377) (@lem8135376 _144007 _144038 P f P' g a h1)). Qed.
Lemma lem8135381 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : ((k f a) = (k g a)) = ((k f a) = (k g a)).
Proof. exact (eq_refl ((k f a) = (k g a))). Qed.
Lemma lem8135382 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term352 _144007 _144038 _144063 P P' f k g a) = (term412 _144007 _144038 _144063 P f k g a).
Proof. exact (MK_COMB (@lem8135378 _144007 _144038 P f P' g a h1) (@lem8135381 _144007 _144038 _144063 P f k g a)). Qed.
Lemma lem8135384 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem8135385 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term412 _144007 _144038 _144063 P f k g a) = True.
Proof. exact (@lem8135384 ((k f a) = (k g a))). Qed.
Lemma lem8135386 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term352 _144007 _144038 _144063 P P' f k g a) = True.
Proof. exact (TRANS (@lem8135382 _144007 _144038 _144063 P f k P' g a h1) (@lem8135385 _144007 _144038 _144063 P f k g a)). Qed.
Lemma lem8135387 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term353 _144007 _144038 _144063 P h P' f k g a) = (term438 _144007 _144038 _144063 P P' f h g a).
Proof. exact (MK_COMB (@lem8135363 _144007 _144038 _144063 P f h P' g a h1) (@lem8135386 _144007 _144038 _144063 P f k P' g a h1)). Qed.
Lemma lem8135389 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem8135390 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term438 _144007 _144038 _144063 P P' f h g a) = (term435 _144007 _144038 _144063 P P' f h g a).
Proof. exact (@lem8135389 (term435 _144007 _144038 _144063 P P' f h g a)). Qed.
Lemma lem8135393 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term353 _144007 _144038 _144063 P h P' f k g a) = (term435 _144007 _144038 _144063 P P' f h g a).
Proof. exact (TRANS (@lem8135387 _144007 _144038 _144063 P k f h P' g a h1) (@lem8135390 _144007 _144038 _144063 P P' f h g a)). Qed.
Lemma lem8135394 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term354 _144007 _144038 _144063 P h P' f k g a) = (term439 _144007 _144038 _144063 P P' f h g a).
Proof. exact (MK_COMB (@lem8135345 _144007 _144038 P f P' g a h1) (@lem8135393 _144007 _144038 _144063 P k f h P' g a h1)). Qed.
Lemma lem8135397 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8135398 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term355 _144007 _144038 _144063 P h P' f k g a) = (term440 _144007 _144038 _144063 P P' f h g a).
Proof. exact (MK_COMB (@lem8135397) (@lem8135394 _144007 _144038 _144063 P k f h P' g a h1)). Qed.
Lemma lem8135400 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (P' g a) = True.
Proof. exact (h1). Qed.
Lemma lem8135401 {_144063 : Type'} : (@COND _144063) = (@COND _144063).
Proof. exact (eq_refl (@COND _144063)). Qed.
Lemma lem8135402 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term418 _144007 _144038 _144063 P P' g a) = (@COND _144063 True).
Proof. exact (MK_COMB (@lem8135401 _144063) (@lem8135400 _144007 _144038 P P' g a h1)). Qed.
Lemma lem8135403 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (h g a) = (h g a).
Proof. exact (eq_refl (h g a)). Qed.
Lemma lem8135404 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term419 _144007 _144038 _144063 P P' h g a) = (term441 _144007 _144038 _144063 P h g a).
Proof. exact (MK_COMB (@lem8135402 _144007 _144038 _144063 P P' g a h1) (@lem8135403 _144007 _144038 _144063 P h g a)). Qed.
Lemma lem8135405 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (k g a) = (k g a).
Proof. exact (eq_refl (k g a)). Qed.
Lemma lem8135406 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term246 _144007 _144038 _144063 P P' h k g a) = (term442 _144007 _144038 _144063 P h k g a).
Proof. exact (MK_COMB (@lem8135404 _144007 _144038 _144063 P h P' g a h1) (@lem8135405 _144007 _144038 _144063 P k g a)). Qed.
Lemma lem8135408 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8135409 {_144063 : Type'} (t2 : _144063) (t1 : _144063) : (@COND _144063 True t1 t2) = t1.
Proof. exact (@lem8135408 _144063 t2 t1). Qed.
Lemma lem8135410 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term442 _144007 _144038 _144063 P h k g a) = (h g a).
Proof. exact (@lem8135409 _144063 (k g a) (h g a)). Qed.
Lemma lem8135411 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term246 _144007 _144038 _144063 P P' h k g a) = (h g a).
Proof. exact (TRANS (@lem8135406 _144007 _144038 _144063 P h k P' g a h1) (@lem8135410 _144007 _144038 _144063 P k h g a)). Qed.
Lemma lem8135412 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (a : P) : (term251 _144007 _144038 _144063 P P' h k f a) = (term251 _144007 _144038 _144063 P P' h k f a).
Proof. exact (eq_refl (term251 _144007 _144038 _144063 P P' h k f a)). Qed.
Lemma lem8135413 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : ((term246 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k g a)) = ((term246 _144007 _144038 _144063 P P' h k f a) = (h g a)).
Proof. exact (MK_COMB (@lem8135412 _144007 _144038 _144063 P P' h k f a) (@lem8135411 _144007 _144038 _144063 P k h P' g a h1)). Qed.
Lemma lem8135416 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term357 _144007 _144038 _144063 P f P' h k g a) = (term443 _144007 _144038 _144063 P P' k f h g a).
Proof. exact (MK_COMB (@lem8135398 _144007 _144038 _144063 P k f h P' g a h1) (@lem8135413 _144007 _144038 _144063 P k f h P' g a h1)). Qed.
Lemma lem8135419 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) : (term367 _144006 _144007 _144038 P lt2 s a f g) = (term367 _144006 _144007 _144038 P lt2 s a f g).
Proof. exact (eq_refl (term367 _144006 _144007 _144038 P lt2 s a f g)). Qed.
Lemma lem8135420 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term369 _144006 _144007 _144038 _144063 P lt2 s f P' h k g a) = (term444 _144006 _144007 _144038 _144063 P lt2 s P' k f h g a).
Proof. exact (MK_COMB (@lem8135419 _144006 _144007 _144038 P lt2 s a f g) (@lem8135416 _144007 _144038 _144063 P k f h P' g a h1)). Qed.
Lemma lem8135423 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term370 _144007 _144038 P p g a) = (term370 _144007 _144038 P p g a).
Proof. exact (eq_refl (term370 _144007 _144038 P p g a)). Qed.
Lemma lem8135424 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term372 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a) = (term445 _144006 _144007 _144038 _144063 P p lt2 s P' k f h g a).
Proof. exact (MK_COMB (@lem8135423 _144007 _144038 P p g a) (@lem8135420 _144006 _144007 _144038 _144063 P lt2 s k f h P' g a h1)). Qed.
Lemma lem8135427 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term370 _144007 _144038 P p f a) = (term370 _144007 _144038 P p f a).
Proof. exact (eq_refl (term370 _144007 _144038 P p f a)). Qed.
Lemma lem8135428 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term373 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a) = (term446 _144006 _144007 _144038 _144063 P p lt2 s P' k f h g a).
Proof. exact (MK_COMB (@lem8135427 _144007 _144038 P p f a) (@lem8135424 _144006 _144007 _144038 _144063 P p lt2 s k f h P' g a h1)). Qed.
Lemma lem8135431 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term375 _144006 _144007 _144038 _144063 P lt2 s f P' h k g a) = (term447 _144006 _144007 _144038 _144063 P lt2 s P' k f h g a).
Proof. exact (fun_ext (fun p : type560 _144007 _144038 P => @lem8135428 _144006 _144007 _144038 _144063 P p lt2 s k f h P' g a h1)). Qed.
Lemma lem8135432 {_144007 _144038 P : Type'} : (@all ((_144007 -> _144038) -> P -> Prop)) = (@all ((_144007 -> _144038) -> P -> Prop)).
Proof. exact (eq_refl (@all ((_144007 -> _144038) -> P -> Prop))). Qed.
Lemma lem8135433 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term377 _144006 _144007 _144038 _144063 P lt2 s f P' h k g a) = (term448 _144006 _144007 _144038 _144063 P lt2 s P' k f h g a).
Proof. exact (MK_COMB (@lem8135432 _144007 _144038 P) (@lem8135431 _144006 _144007 _144038 _144063 P lt2 s k f h P' g a h1)). Qed.
Lemma lem8135438 {_144006 _144007 _144038 _144063 P : Type'} (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term379 _144006 _144007 _144038 _144063 P s f P' h k g a) = (term449 _144006 _144007 _144038 _144063 P s P' k f h g a).
Proof. exact (fun_ext (fun lt2 : type1470 _144006 _144007 => @lem8135433 _144006 _144007 _144038 _144063 P lt2 s k f h P' g a h1)). Qed.
Lemma lem8135439 {_144006 _144007 : Type'} : (@all (_144007 -> _144006 -> Prop)) = (@all (_144007 -> _144006 -> Prop)).
Proof. exact (eq_refl (@all (_144007 -> _144006 -> Prop))). Qed.
Lemma lem8135440 {_144006 _144007 _144038 _144063 P : Type'} (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term381 _144006 _144007 _144038 _144063 P s f P' h k g a) = (term450 _144006 _144007 _144038 _144063 P s P' k f h g a).
Proof. exact (MK_COMB (@lem8135439 _144006 _144007) (@lem8135438 _144006 _144007 _144038 _144063 P s k f h P' g a h1)). Qed.
Lemma lem8135445 {_144006 _144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term383 _144006 _144007 _144038 _144063 P f P' h k g a) = (term451 _144006 _144007 _144038 _144063 P P' k f h g a).
Proof. exact (fun_ext (fun s : P -> _144006 => @lem8135440 _144006 _144007 _144038 _144063 P s k f h P' g a h1)). Qed.
Lemma lem8135446 {_144006 P : Type'} : (@all (P -> _144006)) = (@all (P -> _144006)).
Proof. exact (eq_refl (@all (P -> _144006))). Qed.
Lemma lem8135447 {_144006 _144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term385 _144006 _144007 _144038 _144063 P f P' h k g a) = (term452 _144006 _144007 _144038 _144063 P P' k f h g a).
Proof. exact (MK_COMB (@lem8135446 _144006 P) (@lem8135445 _144006 _144007 _144038 _144063 P k f h P' g a h1)). Qed.
Lemma lem8135452 {_144006 _144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term387 _144006 _144007 _144038 _144063 P P' h k g a) = (term453 _144006 _144007 _144038 _144063 P P' k h g a).
Proof. exact (fun_ext (fun f : _144007 -> _144038 => @lem8135447 _144006 _144007 _144038 _144063 P k f h P' g a h1)). Qed.
Lemma lem8135453 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8135454 {_144006 _144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : (P' g a) = True) : (term389 _144006 _144007 _144038 _144063 P P' h k g a) = (term454 _144006 _144007 _144038 _144063 P P' k h g a).
Proof. exact (MK_COMB (@lem8135453 _144007 _144038) (@lem8135452 _144006 _144007 _144038 _144063 P k h P' g a h1)). Qed.
Lemma lem8135459 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : term455 _144006 _144007 _144038 _144063 P P' k h g a.
Proof. exact (fun h0 : (P' g a) = True => @lem8135454 _144006 _144007 _144038 _144063 P k h P' g a h0). Qed.
Lemma lem8135460 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : term456 _144006 _144007 _144038 _144063 P P' k h g a.
Proof. exact (conj (@lem8135327 _144006 _144007 _144038 _144063 P P' h k g a) (@lem8135459 _144006 _144007 _144038 _144063 P P' k h g a)). Qed.
Lemma lem8135462 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term457 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem8135463 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : term458 _144006 _144007 _144038 _144063 P P' h k g a.
Proof. exact (@lem8135462 (term389 _144006 _144007 _144038 _144063 P P' h k g a) (term454 _144006 _144007 _144038 _144063 P P' k h g a) (P' g a) (term433 _144006 _144007 _144038 _144063 P P' h k g a)). Qed.
Lemma lem8135478 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term389 _144006 _144007 _144038 _144063 P P' h k g a) = (term459 _144006 _144007 _144038 _144063 P P' h k g a).
Proof. exact (@lem8135463 _144006 _144007 _144038 _144063 P P' h k g a (@lem8135460 _144006 _144007 _144038 _144063 P P' k h g a)). Qed.
Lemma lem8135490 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (P' f a) = False.
Proof. exact (h1). Qed.
Lemma lem8135491 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8135492 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term346 _144007 _144038 P P' f a) = (~ False).
Proof. exact (MK_COMB (@lem8135491) (@lem8135490 _144007 _144038 P P' f a h1)). Qed.
Lemma lem8135494 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem8135495 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term346 _144007 _144038 P P' f a) = True.
Proof. exact (TRANS (@lem8135492 _144007 _144038 P P' f a h1) (@lem8135494)). Qed.
Lemma lem8135496 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8135497 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term348 _144007 _144038 P P' f a) = (and True).
Proof. exact (MK_COMB (@lem8135496) (@lem8135495 _144007 _144038 P P' f a h1)). Qed.
Lemma lem8135499 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (P' f a) = False.
Proof. exact (h1). Qed.
Lemma lem8135500 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8135501 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term346 _144007 _144038 P P' f a) = (~ False).
Proof. exact (MK_COMB (@lem8135500) (@lem8135499 _144007 _144038 P P' f a h1)). Qed.
Lemma lem8135503 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem8135504 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term346 _144007 _144038 P P' f a) = True.
Proof. exact (TRANS (@lem8135501 _144007 _144038 P P' f a h1) (@lem8135503)). Qed.
Lemma lem8135505 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8135506 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term413 _144007 _144038 P P' f a) = (imp True).
Proof. exact (MK_COMB (@lem8135505) (@lem8135504 _144007 _144038 P P' f a h1)). Qed.
Lemma lem8135509 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : ((k f a) = (k g a)) = ((k f a) = (k g a)).
Proof. exact (eq_refl ((k f a) = (k g a))). Qed.
Lemma lem8135510 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term414 _144007 _144038 _144063 P P' f k g a) = (term460 _144007 _144038 _144063 P f k g a).
Proof. exact (MK_COMB (@lem8135506 _144007 _144038 P P' f a h1) (@lem8135509 _144007 _144038 _144063 P f k g a)). Qed.
Lemma lem8135512 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem8135513 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term460 _144007 _144038 _144063 P f k g a) = ((k f a) = (k g a)).
Proof. exact (@lem8135512 ((k f a) = (k g a))). Qed.
Lemma lem8135516 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term414 _144007 _144038 _144063 P P' f k g a) = ((k f a) = (k g a)).
Proof. exact (TRANS (@lem8135510 _144007 _144038 _144063 P k g P' f a h1) (@lem8135513 _144007 _144038 _144063 P f k g a)). Qed.
Lemma lem8135517 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term416 _144007 _144038 _144063 P P' f k g a) = (term461 _144007 _144038 _144063 P f k g a).
Proof. exact (MK_COMB (@lem8135497 _144007 _144038 P P' f a h1) (@lem8135516 _144007 _144038 _144063 P k g P' f a h1)). Qed.
Lemma lem8135519 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8135520 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term461 _144007 _144038 _144063 P f k g a) = ((k f a) = (k g a)).
Proof. exact (@lem8135519 ((k f a) = (k g a))). Qed.
Lemma lem8135523 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term416 _144007 _144038 _144063 P P' f k g a) = ((k f a) = (k g a)).
Proof. exact (TRANS (@lem8135517 _144007 _144038 _144063 P k g P' f a h1) (@lem8135520 _144007 _144038 _144063 P f k g a)). Qed.
Lemma lem8135524 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8135525 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term417 _144007 _144038 _144063 P P' f k g a) = (term462 _144007 _144038 _144063 P f k g a).
Proof. exact (MK_COMB (@lem8135524) (@lem8135523 _144007 _144038 _144063 P k g P' f a h1)). Qed.
Lemma lem8135527 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (P' f a) = False.
Proof. exact (h1). Qed.
Lemma lem8135528 {_144063 : Type'} : (@COND _144063) = (@COND _144063).
Proof. exact (eq_refl (@COND _144063)). Qed.
Lemma lem8135529 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term418 _144007 _144038 _144063 P P' f a) = (@COND _144063 False).
Proof. exact (MK_COMB (@lem8135528 _144063) (@lem8135527 _144007 _144038 P P' f a h1)). Qed.
Lemma lem8135530 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (a : P) : (h f a) = (h f a).
Proof. exact (eq_refl (h f a)). Qed.
Lemma lem8135531 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term419 _144007 _144038 _144063 P P' h f a) = (term420 _144007 _144038 _144063 P h f a).
Proof. exact (MK_COMB (@lem8135529 _144007 _144038 _144063 P P' f a h1) (@lem8135530 _144007 _144038 _144063 P h f a)). Qed.
Lemma lem8135532 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (a : P) : (k f a) = (k f a).
Proof. exact (eq_refl (k f a)). Qed.
Lemma lem8135533 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term246 _144007 _144038 _144063 P P' h k f a) = (term421 _144007 _144038 _144063 P h k f a).
Proof. exact (MK_COMB (@lem8135531 _144007 _144038 _144063 P h P' f a h1) (@lem8135532 _144007 _144038 _144063 P k f a)). Qed.
Lemma lem8135535 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8135536 {_144063 : Type'} (t1 : _144063) (t2 : _144063) : (@COND _144063 False t1 t2) = t2.
Proof. exact (@lem8135535 _144063 t1 t2). Qed.
Lemma lem8135537 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (a : P) : (term421 _144007 _144038 _144063 P h k f a) = (k f a).
Proof. exact (@lem8135536 _144063 (h f a) (k f a)). Qed.
Lemma lem8135538 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term246 _144007 _144038 _144063 P P' h k f a) = (k f a).
Proof. exact (TRANS (@lem8135533 _144007 _144038 _144063 P h k P' f a h1) (@lem8135537 _144007 _144038 _144063 P h k f a)). Qed.
Lemma lem8135539 {_144063 : Type'} : (@eq _144063) = (@eq _144063).
Proof. exact (eq_refl (@eq _144063)). Qed.
Lemma lem8135540 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term251 _144007 _144038 _144063 P P' h k f a) = (term463 _144007 _144038 _144063 P k f a).
Proof. exact (MK_COMB (@lem8135539 _144063) (@lem8135538 _144007 _144038 _144063 P h k P' f a h1)). Qed.
Lemma lem8135541 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (k g a) = (k g a).
Proof. exact (eq_refl (k g a)). Qed.
Lemma lem8135542 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : ((term246 _144007 _144038 _144063 P P' h k f a) = (k g a)) = ((k f a) = (k g a)).
Proof. exact (MK_COMB (@lem8135540 _144007 _144038 _144063 P h k P' f a h1) (@lem8135541 _144007 _144038 _144063 P k g a)). Qed.
Lemma lem8135545 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term422 _144007 _144038 _144063 P P' h f k g a) = (term464 _144007 _144038 _144063 P f k g a).
Proof. exact (MK_COMB (@lem8135525 _144007 _144038 _144063 P k g P' f a h1) (@lem8135542 _144007 _144038 _144063 P h k g P' f a h1)). Qed.
Lemma lem8135549 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem8135550 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term464 _144007 _144038 _144063 P f k g a) = True.
Proof. exact (@lem8135549 ((k f a) = (k g a))). Qed.
Lemma lem8135551 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term422 _144007 _144038 _144063 P P' h f k g a) = True.
Proof. exact (TRANS (@lem8135545 _144007 _144038 _144063 P h k g P' f a h1) (@lem8135550 _144007 _144038 _144063 P f k g a)). Qed.
Lemma lem8135552 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) : (term367 _144006 _144007 _144038 P lt2 s a f g) = (term367 _144006 _144007 _144038 P lt2 s a f g).
Proof. exact (eq_refl (term367 _144006 _144007 _144038 P lt2 s a f g)). Qed.
Lemma lem8135553 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term423 _144006 _144007 _144038 _144063 P lt2 s P' h f k g a) = (term465 _144006 _144007 _144038 P lt2 s a f g).
Proof. exact (MK_COMB (@lem8135552 _144006 _144007 _144038 P lt2 s a f g) (@lem8135551 _144007 _144038 _144063 P h k g P' f a h1)). Qed.
Lemma lem8135555 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem8135556 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) : (term465 _144006 _144007 _144038 P lt2 s a f g) = True.
Proof. exact (@lem8135555 (term43 _144006 _144007 _144038 P lt2 s a f g)). Qed.
Lemma lem8135557 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term423 _144006 _144007 _144038 _144063 P lt2 s P' h f k g a) = True.
Proof. exact (TRANS (@lem8135553 _144006 _144007 _144038 _144063 P h k lt2 s g P' f a h1) (@lem8135556 _144006 _144007 _144038 P lt2 s a f g)). Qed.
Lemma lem8135558 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term370 _144007 _144038 P p g a) = (term370 _144007 _144038 P p g a).
Proof. exact (eq_refl (term370 _144007 _144038 P p g a)). Qed.
Lemma lem8135559 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term424 _144006 _144007 _144038 _144063 P p lt2 s P' h f k g a) = (term466 _144007 _144038 P p g a).
Proof. exact (MK_COMB (@lem8135558 _144007 _144038 P p g a) (@lem8135557 _144006 _144007 _144038 _144063 P lt2 s h k g P' f a h1)). Qed.
Lemma lem8135561 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem8135562 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term466 _144007 _144038 P p g a) = True.
Proof. exact (@lem8135561 (p g a)). Qed.
Lemma lem8135563 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term424 _144006 _144007 _144038 _144063 P p lt2 s P' h f k g a) = True.
Proof. exact (TRANS (@lem8135559 _144006 _144007 _144038 _144063 P lt2 s h k p g P' f a h1) (@lem8135562 _144007 _144038 P p g a)). Qed.
Lemma lem8135564 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term370 _144007 _144038 P p f a) = (term370 _144007 _144038 P p f a).
Proof. exact (eq_refl (term370 _144007 _144038 P p f a)). Qed.
Lemma lem8135565 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term425 _144006 _144007 _144038 _144063 P p lt2 s P' h f k g a) = (term466 _144007 _144038 P p f a).
Proof. exact (MK_COMB (@lem8135564 _144007 _144038 P p f a) (@lem8135563 _144006 _144007 _144038 _144063 P p lt2 s h k g P' f a h1)). Qed.
Lemma lem8135567 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem8135568 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term466 _144007 _144038 P p f a) = True.
Proof. exact (@lem8135567 (p f a)). Qed.
Lemma lem8135569 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term425 _144006 _144007 _144038 _144063 P p lt2 s P' h f k g a) = True.
Proof. exact (TRANS (@lem8135565 _144006 _144007 _144038 _144063 P lt2 s h k g p P' f a h1) (@lem8135568 _144007 _144038 P p f a)). Qed.
Lemma lem8135570 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term426 _144006 _144007 _144038 _144063 P lt2 s P' h f k g a) = (term467 _144007 _144038 P).
Proof. exact (fun_ext (fun p : type560 _144007 _144038 P => @lem8135569 _144006 _144007 _144038 _144063 P p lt2 s h k g P' f a h1)). Qed.
Lemma lem8135571 {_144007 _144038 P : Type'} : (@all ((_144007 -> _144038) -> P -> Prop)) = (@all ((_144007 -> _144038) -> P -> Prop)).
Proof. exact (eq_refl (@all ((_144007 -> _144038) -> P -> Prop))). Qed.
Lemma lem8135572 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term427 _144006 _144007 _144038 _144063 P lt2 s P' h f k g a) = (term468 _144007 _144038 P).
Proof. exact (MK_COMB (@lem8135571 _144007 _144038 P) (@lem8135570 _144006 _144007 _144038 _144063 P lt2 s h k g P' f a h1)). Qed.
Lemma lem8135574 {A : Type'} (t : Prop) : (term337 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8135575 {_144007 _144038 P : Type'} (t : Prop) : (term469 _144007 _144038 P t) = t.
Proof. exact (@lem8135574 (type560 _144007 _144038 P) t). Qed.
Lemma lem8135576 {_144007 _144038 P : Type'} : (term468 _144007 _144038 P) = True.
Proof. exact (@lem8135575 _144007 _144038 P True). Qed.
Lemma lem8135577 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term427 _144006 _144007 _144038 _144063 P lt2 s P' h f k g a) = True.
Proof. exact (TRANS (@lem8135572 _144006 _144007 _144038 _144063 P lt2 s h k g P' f a h1) (@lem8135576 _144007 _144038 P)). Qed.
Lemma lem8135578 {_144006 _144007 _144038 _144063 P : Type'} (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term428 _144006 _144007 _144038 _144063 P s P' h f k g a) = (term470 _144006 _144007).
Proof. exact (fun_ext (fun lt2 : type1470 _144006 _144007 => @lem8135577 _144006 _144007 _144038 _144063 P lt2 s h k g P' f a h1)). Qed.
Lemma lem8135579 {_144006 _144007 : Type'} : (@all (_144007 -> _144006 -> Prop)) = (@all (_144007 -> _144006 -> Prop)).
Proof. exact (eq_refl (@all (_144007 -> _144006 -> Prop))). Qed.
Lemma lem8135580 {_144006 _144007 _144038 _144063 P : Type'} (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term429 _144006 _144007 _144038 _144063 P s P' h f k g a) = (term471 _144006 _144007).
Proof. exact (MK_COMB (@lem8135579 _144006 _144007) (@lem8135578 _144006 _144007 _144038 _144063 P s h k g P' f a h1)). Qed.
Lemma lem8135582 {A : Type'} (t : Prop) : (term337 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8135583 {_144006 _144007 : Type'} (t : Prop) : (term472 _144006 _144007 t) = t.
Proof. exact (@lem8135582 (type1470 _144006 _144007) t). Qed.
Lemma lem8135584 {_144006 _144007 : Type'} : (term471 _144006 _144007) = True.
Proof. exact (@lem8135583 _144006 _144007 True). Qed.
Lemma lem8135585 {_144006 _144007 _144038 _144063 P : Type'} (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term429 _144006 _144007 _144038 _144063 P s P' h f k g a) = True.
Proof. exact (TRANS (@lem8135580 _144006 _144007 _144038 _144063 P s h k g P' f a h1) (@lem8135584 _144006 _144007)). Qed.
Lemma lem8135586 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term430 _144006 _144007 _144038 _144063 P P' h f k g a) = (term473 _144006 P).
Proof. exact (fun_ext (fun s : P -> _144006 => @lem8135585 _144006 _144007 _144038 _144063 P s h k g P' f a h1)). Qed.
Lemma lem8135587 {_144006 P : Type'} : (@all (P -> _144006)) = (@all (P -> _144006)).
Proof. exact (eq_refl (@all (P -> _144006))). Qed.
Lemma lem8135588 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term431 _144006 _144007 _144038 _144063 P P' h f k g a) = (term474 _144006 P).
Proof. exact (MK_COMB (@lem8135587 _144006 P) (@lem8135586 _144006 _144007 _144038 _144063 P h k g P' f a h1)). Qed.
Lemma lem8135590 {A : Type'} (t : Prop) : (term337 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8135591 {_144006 P : Type'} (t : Prop) : (term475 _144006 P t) = t.
Proof. exact (@lem8135590 (P -> _144006) t). Qed.
Lemma lem8135592 {_144006 P : Type'} : (term474 _144006 P) = True.
Proof. exact (@lem8135591 _144006 P True). Qed.
Lemma lem8135593 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term431 _144006 _144007 _144038 _144063 P P' h f k g a) = True.
Proof. exact (TRANS (@lem8135588 _144006 _144007 _144038 _144063 P h k g P' f a h1) (@lem8135592 _144006 P)). Qed.
Lemma lem8135594 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : term476 _144006 _144007 _144038 _144063 P P' h f k g a.
Proof. exact (fun h0 : (P' f a) = False => @lem8135593 _144006 _144007 _144038 _144063 P h k g P' f a h0). Qed.
Lemma lem8135604 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (P' f a) = True.
Proof. exact (h1). Qed.
Lemma lem8135605 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8135606 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term346 _144007 _144038 P P' f a) = (~ True).
Proof. exact (MK_COMB (@lem8135605) (@lem8135604 _144007 _144038 P P' f a h1)). Qed.
Lemma lem8135608 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem8135609 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term346 _144007 _144038 P P' f a) = False.
Proof. exact (TRANS (@lem8135606 _144007 _144038 P P' f a h1) (@lem8135608)). Qed.
Lemma lem8135610 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8135611 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term348 _144007 _144038 P P' f a) = (and False).
Proof. exact (MK_COMB (@lem8135610) (@lem8135609 _144007 _144038 P P' f a h1)). Qed.
Lemma lem8135613 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (P' f a) = True.
Proof. exact (h1). Qed.
Lemma lem8135614 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8135615 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term346 _144007 _144038 P P' f a) = (~ True).
Proof. exact (MK_COMB (@lem8135614) (@lem8135613 _144007 _144038 P P' f a h1)). Qed.
Lemma lem8135617 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem8135618 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term346 _144007 _144038 P P' f a) = False.
Proof. exact (TRANS (@lem8135615 _144007 _144038 P P' f a h1) (@lem8135617)). Qed.
Lemma lem8135619 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8135620 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term413 _144007 _144038 P P' f a) = (imp False).
Proof. exact (MK_COMB (@lem8135619) (@lem8135618 _144007 _144038 P P' f a h1)). Qed.
Lemma lem8135623 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : ((k f a) = (k g a)) = ((k f a) = (k g a)).
Proof. exact (eq_refl ((k f a) = (k g a))). Qed.
Lemma lem8135624 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term414 _144007 _144038 _144063 P P' f k g a) = (term412 _144007 _144038 _144063 P f k g a).
Proof. exact (MK_COMB (@lem8135620 _144007 _144038 P P' f a h1) (@lem8135623 _144007 _144038 _144063 P f k g a)). Qed.
Lemma lem8135626 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem8135627 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term412 _144007 _144038 _144063 P f k g a) = True.
Proof. exact (@lem8135626 ((k f a) = (k g a))). Qed.
Lemma lem8135628 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term414 _144007 _144038 _144063 P P' f k g a) = True.
Proof. exact (TRANS (@lem8135624 _144007 _144038 _144063 P k g P' f a h1) (@lem8135627 _144007 _144038 _144063 P f k g a)). Qed.
Lemma lem8135629 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term416 _144007 _144038 _144063 P P' f k g a) = (False /\ True).
Proof. exact (MK_COMB (@lem8135611 _144007 _144038 P P' f a h1) (@lem8135628 _144007 _144038 _144063 P k g P' f a h1)). Qed.
Lemma lem8135631 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8135632 : (False /\ True) = False.
Proof. exact (@lem8135631 True). Qed.
Lemma lem8135633 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term416 _144007 _144038 _144063 P P' f k g a) = False.
Proof. exact (TRANS (@lem8135629 _144007 _144038 _144063 P k g P' f a h1) (@lem8135632)). Qed.
Lemma lem8135634 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8135635 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term417 _144007 _144038 _144063 P P' f k g a) = (imp False).
Proof. exact (MK_COMB (@lem8135634) (@lem8135633 _144007 _144038 _144063 P k g P' f a h1)). Qed.
Lemma lem8135637 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (P' f a) = True.
Proof. exact (h1). Qed.
Lemma lem8135638 {_144063 : Type'} : (@COND _144063) = (@COND _144063).
Proof. exact (eq_refl (@COND _144063)). Qed.
Lemma lem8135639 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term418 _144007 _144038 _144063 P P' f a) = (@COND _144063 True).
Proof. exact (MK_COMB (@lem8135638 _144063) (@lem8135637 _144007 _144038 P P' f a h1)). Qed.
Lemma lem8135640 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (a : P) : (h f a) = (h f a).
Proof. exact (eq_refl (h f a)). Qed.
Lemma lem8135641 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term419 _144007 _144038 _144063 P P' h f a) = (term441 _144007 _144038 _144063 P h f a).
Proof. exact (MK_COMB (@lem8135639 _144007 _144038 _144063 P P' f a h1) (@lem8135640 _144007 _144038 _144063 P h f a)). Qed.
Lemma lem8135642 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (a : P) : (k f a) = (k f a).
Proof. exact (eq_refl (k f a)). Qed.
Lemma lem8135643 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term246 _144007 _144038 _144063 P P' h k f a) = (term442 _144007 _144038 _144063 P h k f a).
Proof. exact (MK_COMB (@lem8135641 _144007 _144038 _144063 P h P' f a h1) (@lem8135642 _144007 _144038 _144063 P k f a)). Qed.
Lemma lem8135645 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8135646 {_144063 : Type'} (t2 : _144063) (t1 : _144063) : (@COND _144063 True t1 t2) = t1.
Proof. exact (@lem8135645 _144063 t2 t1). Qed.
Lemma lem8135647 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (a : P) : (term442 _144007 _144038 _144063 P h k f a) = (h f a).
Proof. exact (@lem8135646 _144063 (k f a) (h f a)). Qed.
Lemma lem8135648 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term246 _144007 _144038 _144063 P P' h k f a) = (h f a).
Proof. exact (TRANS (@lem8135643 _144007 _144038 _144063 P h k P' f a h1) (@lem8135647 _144007 _144038 _144063 P k h f a)). Qed.
Lemma lem8135649 {_144063 : Type'} : (@eq _144063) = (@eq _144063).
Proof. exact (eq_refl (@eq _144063)). Qed.
Lemma lem8135650 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term251 _144007 _144038 _144063 P P' h k f a) = (term463 _144007 _144038 _144063 P h f a).
Proof. exact (MK_COMB (@lem8135649 _144063) (@lem8135648 _144007 _144038 _144063 P k h P' f a h1)). Qed.
Lemma lem8135651 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (k g a) = (k g a).
Proof. exact (eq_refl (k g a)). Qed.
Lemma lem8135652 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : ((term246 _144007 _144038 _144063 P P' h k f a) = (k g a)) = ((h f a) = (k g a)).
Proof. exact (MK_COMB (@lem8135650 _144007 _144038 _144063 P k h P' f a h1) (@lem8135651 _144007 _144038 _144063 P k g a)). Qed.
Lemma lem8135655 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term422 _144007 _144038 _144063 P P' h f k g a) = (term477 _144007 _144038 _144063 P h f k g a).
Proof. exact (MK_COMB (@lem8135635 _144007 _144038 _144063 P k g P' f a h1) (@lem8135652 _144007 _144038 _144063 P h k g P' f a h1)). Qed.
Lemma lem8135657 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem8135658 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term477 _144007 _144038 _144063 P h f k g a) = True.
Proof. exact (@lem8135657 ((h f a) = (k g a))). Qed.
Lemma lem8135659 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term422 _144007 _144038 _144063 P P' h f k g a) = True.
Proof. exact (TRANS (@lem8135655 _144007 _144038 _144063 P h k g P' f a h1) (@lem8135658 _144007 _144038 _144063 P h f k g a)). Qed.
Lemma lem8135660 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) : (term367 _144006 _144007 _144038 P lt2 s a f g) = (term367 _144006 _144007 _144038 P lt2 s a f g).
Proof. exact (eq_refl (term367 _144006 _144007 _144038 P lt2 s a f g)). Qed.
Lemma lem8135661 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term423 _144006 _144007 _144038 _144063 P lt2 s P' h f k g a) = (term465 _144006 _144007 _144038 P lt2 s a f g).
Proof. exact (MK_COMB (@lem8135660 _144006 _144007 _144038 P lt2 s a f g) (@lem8135659 _144007 _144038 _144063 P h k g P' f a h1)). Qed.
Lemma lem8135663 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem8135664 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) : (term465 _144006 _144007 _144038 P lt2 s a f g) = True.
Proof. exact (@lem8135663 (term43 _144006 _144007 _144038 P lt2 s a f g)). Qed.
Lemma lem8135665 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term423 _144006 _144007 _144038 _144063 P lt2 s P' h f k g a) = True.
Proof. exact (TRANS (@lem8135661 _144006 _144007 _144038 _144063 P h k lt2 s g P' f a h1) (@lem8135664 _144006 _144007 _144038 P lt2 s a f g)). Qed.
Lemma lem8135666 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term370 _144007 _144038 P p g a) = (term370 _144007 _144038 P p g a).
Proof. exact (eq_refl (term370 _144007 _144038 P p g a)). Qed.
Lemma lem8135667 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term424 _144006 _144007 _144038 _144063 P p lt2 s P' h f k g a) = (term466 _144007 _144038 P p g a).
Proof. exact (MK_COMB (@lem8135666 _144007 _144038 P p g a) (@lem8135665 _144006 _144007 _144038 _144063 P lt2 s h k g P' f a h1)). Qed.
Lemma lem8135669 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem8135670 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term466 _144007 _144038 P p g a) = True.
Proof. exact (@lem8135669 (p g a)). Qed.
Lemma lem8135671 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term424 _144006 _144007 _144038 _144063 P p lt2 s P' h f k g a) = True.
Proof. exact (TRANS (@lem8135667 _144006 _144007 _144038 _144063 P lt2 s h k p g P' f a h1) (@lem8135670 _144007 _144038 P p g a)). Qed.
Lemma lem8135672 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term370 _144007 _144038 P p f a) = (term370 _144007 _144038 P p f a).
Proof. exact (eq_refl (term370 _144007 _144038 P p f a)). Qed.
Lemma lem8135673 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term425 _144006 _144007 _144038 _144063 P p lt2 s P' h f k g a) = (term466 _144007 _144038 P p f a).
Proof. exact (MK_COMB (@lem8135672 _144007 _144038 P p f a) (@lem8135671 _144006 _144007 _144038 _144063 P p lt2 s h k g P' f a h1)). Qed.
Lemma lem8135675 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem8135676 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term466 _144007 _144038 P p f a) = True.
Proof. exact (@lem8135675 (p f a)). Qed.
Lemma lem8135677 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term425 _144006 _144007 _144038 _144063 P p lt2 s P' h f k g a) = True.
Proof. exact (TRANS (@lem8135673 _144006 _144007 _144038 _144063 P lt2 s h k g p P' f a h1) (@lem8135676 _144007 _144038 P p f a)). Qed.
Lemma lem8135678 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term426 _144006 _144007 _144038 _144063 P lt2 s P' h f k g a) = (term467 _144007 _144038 P).
Proof. exact (fun_ext (fun p : type560 _144007 _144038 P => @lem8135677 _144006 _144007 _144038 _144063 P p lt2 s h k g P' f a h1)). Qed.
Lemma lem8135679 {_144007 _144038 P : Type'} : (@all ((_144007 -> _144038) -> P -> Prop)) = (@all ((_144007 -> _144038) -> P -> Prop)).
Proof. exact (eq_refl (@all ((_144007 -> _144038) -> P -> Prop))). Qed.
Lemma lem8135680 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term427 _144006 _144007 _144038 _144063 P lt2 s P' h f k g a) = (term468 _144007 _144038 P).
Proof. exact (MK_COMB (@lem8135679 _144007 _144038 P) (@lem8135678 _144006 _144007 _144038 _144063 P lt2 s h k g P' f a h1)). Qed.
Lemma lem8135682 {A : Type'} (t : Prop) : (term337 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8135683 {_144007 _144038 P : Type'} (t : Prop) : (term469 _144007 _144038 P t) = t.
Proof. exact (@lem8135682 (type560 _144007 _144038 P) t). Qed.
Lemma lem8135684 {_144007 _144038 P : Type'} : (term468 _144007 _144038 P) = True.
Proof. exact (@lem8135683 _144007 _144038 P True). Qed.
Lemma lem8135685 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term427 _144006 _144007 _144038 _144063 P lt2 s P' h f k g a) = True.
Proof. exact (TRANS (@lem8135680 _144006 _144007 _144038 _144063 P lt2 s h k g P' f a h1) (@lem8135684 _144007 _144038 P)). Qed.
Lemma lem8135686 {_144006 _144007 _144038 _144063 P : Type'} (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term428 _144006 _144007 _144038 _144063 P s P' h f k g a) = (term470 _144006 _144007).
Proof. exact (fun_ext (fun lt2 : type1470 _144006 _144007 => @lem8135685 _144006 _144007 _144038 _144063 P lt2 s h k g P' f a h1)). Qed.
Lemma lem8135687 {_144006 _144007 : Type'} : (@all (_144007 -> _144006 -> Prop)) = (@all (_144007 -> _144006 -> Prop)).
Proof. exact (eq_refl (@all (_144007 -> _144006 -> Prop))). Qed.
Lemma lem8135688 {_144006 _144007 _144038 _144063 P : Type'} (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term429 _144006 _144007 _144038 _144063 P s P' h f k g a) = (term471 _144006 _144007).
Proof. exact (MK_COMB (@lem8135687 _144006 _144007) (@lem8135686 _144006 _144007 _144038 _144063 P s h k g P' f a h1)). Qed.
Lemma lem8135690 {A : Type'} (t : Prop) : (term337 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8135691 {_144006 _144007 : Type'} (t : Prop) : (term472 _144006 _144007 t) = t.
Proof. exact (@lem8135690 (type1470 _144006 _144007) t). Qed.
Lemma lem8135692 {_144006 _144007 : Type'} : (term471 _144006 _144007) = True.
Proof. exact (@lem8135691 _144006 _144007 True). Qed.
Lemma lem8135693 {_144006 _144007 _144038 _144063 P : Type'} (s : P -> _144006) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term429 _144006 _144007 _144038 _144063 P s P' h f k g a) = True.
Proof. exact (TRANS (@lem8135688 _144006 _144007 _144038 _144063 P s h k g P' f a h1) (@lem8135692 _144006 _144007)). Qed.
Lemma lem8135694 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term430 _144006 _144007 _144038 _144063 P P' h f k g a) = (term473 _144006 P).
Proof. exact (fun_ext (fun s : P -> _144006 => @lem8135693 _144006 _144007 _144038 _144063 P s h k g P' f a h1)). Qed.
Lemma lem8135695 {_144006 P : Type'} : (@all (P -> _144006)) = (@all (P -> _144006)).
Proof. exact (eq_refl (@all (P -> _144006))). Qed.
Lemma lem8135696 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term431 _144006 _144007 _144038 _144063 P P' h f k g a) = (term474 _144006 P).
Proof. exact (MK_COMB (@lem8135695 _144006 P) (@lem8135694 _144006 _144007 _144038 _144063 P h k g P' f a h1)). Qed.
Lemma lem8135698 {A : Type'} (t : Prop) : (term337 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8135699 {_144006 P : Type'} (t : Prop) : (term475 _144006 P t) = t.
Proof. exact (@lem8135698 (P -> _144006) t). Qed.
Lemma lem8135700 {_144006 P : Type'} : (term474 _144006 P) = True.
Proof. exact (@lem8135699 _144006 P True). Qed.
Lemma lem8135701 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term431 _144006 _144007 _144038 _144063 P P' h f k g a) = True.
Proof. exact (TRANS (@lem8135696 _144006 _144007 _144038 _144063 P h k g P' f a h1) (@lem8135700 _144006 P)). Qed.
Lemma lem8135702 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : term478 _144006 _144007 _144038 _144063 P P' h f k g a.
Proof. exact (fun h0 : (P' f a) = True => @lem8135701 _144006 _144007 _144038 _144063 P h k g P' f a h0). Qed.
Lemma lem8135703 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : term479 _144006 _144007 _144038 _144063 P P' h f k g a.
Proof. exact (conj (@lem8135594 _144006 _144007 _144038 _144063 P P' h f k g a) (@lem8135702 _144006 _144007 _144038 _144063 P P' h f k g a)). Qed.
Lemma lem8135705 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term457 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem8135706 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : term480 _144006 _144007 _144038 _144063 P h k g P' f a.
Proof. exact (@lem8135705 (term431 _144006 _144007 _144038 _144063 P P' h f k g a) True (P' f a) True). Qed.
Lemma lem8135707 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term431 _144006 _144007 _144038 _144063 P P' h f k g a) = (term481 _144007 _144038 P P' f a).
Proof. exact (@lem8135706 _144006 _144007 _144038 _144063 P h k g P' f a (@lem8135703 _144006 _144007 _144038 _144063 P P' h f k g a)). Qed.
Lemma lem8135709 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem8135710 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term482 _144007 _144038 P P' f a) = True.
Proof. exact (@lem8135709 (P' f a)). Qed.
Lemma lem8135712 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem8135713 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term483 _144007 _144038 P P' f a) = True.
Proof. exact (@lem8135712 (term346 _144007 _144038 P P' f a)). Qed.
Lemma lem8135714 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8135715 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term484 _144007 _144038 P P' f a) = (and True).
Proof. exact (MK_COMB (@lem8135714) (@lem8135713 _144007 _144038 P P' f a)). Qed.
Lemma lem8135716 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term481 _144007 _144038 P P' f a) = (True /\ True).
Proof. exact (MK_COMB (@lem8135715 _144007 _144038 P P' f a) (@lem8135710 _144007 _144038 P P' f a)). Qed.
Lemma lem8135718 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8135719 : (True /\ True) = True.
Proof. exact (@lem8135718 True). Qed.
Lemma lem8135720 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term481 _144007 _144038 P P' f a) = True.
Proof. exact (TRANS (@lem8135716 _144007 _144038 P P' f a) (@lem8135719)). Qed.
Lemma lem8135725 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term431 _144006 _144007 _144038 _144063 P P' h f k g a) = True.
Proof. exact (TRANS (@lem8135707 _144006 _144007 _144038 _144063 P h k g P' f a) (@lem8135720 _144007 _144038 P P' f a)). Qed.
Lemma lem8135726 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term432 _144006 _144007 _144038 _144063 P P' h k g a) = (term485 _144007 _144038).
Proof. exact (fun_ext (fun f : _144007 -> _144038 => @lem8135725 _144006 _144007 _144038 _144063 P P' h f k g a)). Qed.
Lemma lem8135727 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8135728 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term433 _144006 _144007 _144038 _144063 P P' h k g a) = (term486 _144007 _144038).
Proof. exact (MK_COMB (@lem8135727 _144007 _144038) (@lem8135726 _144006 _144007 _144038 _144063 P P' h k g a)). Qed.
Lemma lem8135731 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term487 _144007 _144038 P P' g a) = (term487 _144007 _144038 P P' g a).
Proof. exact (eq_refl (term487 _144007 _144038 P P' g a)). Qed.
Lemma lem8135732 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term488 _144006 _144007 _144038 _144063 P P' h k g a) = (term489 _144007 _144038 P P' g a).
Proof. exact (MK_COMB (@lem8135731 _144007 _144038 P P' g a) (@lem8135728 _144006 _144007 _144038 _144063 P P' h k g a)). Qed.
Lemma lem8135744 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (P' f a) = False.
Proof. exact (h1). Qed.
Lemma lem8135745 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8135746 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term333 _144007 _144038 P P' f a) = (and False).
Proof. exact (MK_COMB (@lem8135745) (@lem8135744 _144007 _144038 P P' f a h1)). Qed.
Lemma lem8135748 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (P' f a) = False.
Proof. exact (h1). Qed.
Lemma lem8135749 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8135750 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term370 _144007 _144038 P P' f a) = (imp False).
Proof. exact (MK_COMB (@lem8135749) (@lem8135748 _144007 _144038 P P' f a h1)). Qed.
Lemma lem8135753 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : ((h f a) = (h g a)) = ((h f a) = (h g a)).
Proof. exact (eq_refl ((h f a) = (h g a))). Qed.
Lemma lem8135754 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term435 _144007 _144038 _144063 P P' f h g a) = (term412 _144007 _144038 _144063 P f h g a).
Proof. exact (MK_COMB (@lem8135750 _144007 _144038 P P' f a h1) (@lem8135753 _144007 _144038 _144063 P f h g a)). Qed.
Lemma lem8135756 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem8135757 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term412 _144007 _144038 _144063 P f h g a) = True.
Proof. exact (@lem8135756 ((h f a) = (h g a))). Qed.
Lemma lem8135758 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term435 _144007 _144038 _144063 P P' f h g a) = True.
Proof. exact (TRANS (@lem8135754 _144007 _144038 _144063 P h g P' f a h1) (@lem8135757 _144007 _144038 _144063 P f h g a)). Qed.
Lemma lem8135759 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term439 _144007 _144038 _144063 P P' f h g a) = (False /\ True).
Proof. exact (MK_COMB (@lem8135746 _144007 _144038 P P' f a h1) (@lem8135758 _144007 _144038 _144063 P h g P' f a h1)). Qed.
Lemma lem8135761 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8135762 : (False /\ True) = False.
Proof. exact (@lem8135761 True). Qed.
Lemma lem8135763 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term439 _144007 _144038 _144063 P P' f h g a) = False.
Proof. exact (TRANS (@lem8135759 _144007 _144038 _144063 P h g P' f a h1) (@lem8135762)). Qed.
Lemma lem8135764 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8135765 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term440 _144007 _144038 _144063 P P' f h g a) = (imp False).
Proof. exact (MK_COMB (@lem8135764) (@lem8135763 _144007 _144038 _144063 P h g P' f a h1)). Qed.
Lemma lem8135767 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (P' f a) = False.
Proof. exact (h1). Qed.
Lemma lem8135768 {_144063 : Type'} : (@COND _144063) = (@COND _144063).
Proof. exact (eq_refl (@COND _144063)). Qed.
Lemma lem8135769 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term418 _144007 _144038 _144063 P P' f a) = (@COND _144063 False).
Proof. exact (MK_COMB (@lem8135768 _144063) (@lem8135767 _144007 _144038 P P' f a h1)). Qed.
Lemma lem8135770 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (a : P) : (h f a) = (h f a).
Proof. exact (eq_refl (h f a)). Qed.
Lemma lem8135771 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term419 _144007 _144038 _144063 P P' h f a) = (term420 _144007 _144038 _144063 P h f a).
Proof. exact (MK_COMB (@lem8135769 _144007 _144038 _144063 P P' f a h1) (@lem8135770 _144007 _144038 _144063 P h f a)). Qed.
Lemma lem8135772 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (a : P) : (k f a) = (k f a).
Proof. exact (eq_refl (k f a)). Qed.
Lemma lem8135773 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term246 _144007 _144038 _144063 P P' h k f a) = (term421 _144007 _144038 _144063 P h k f a).
Proof. exact (MK_COMB (@lem8135771 _144007 _144038 _144063 P h P' f a h1) (@lem8135772 _144007 _144038 _144063 P k f a)). Qed.
Lemma lem8135775 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8135776 {_144063 : Type'} (t1 : _144063) (t2 : _144063) : (@COND _144063 False t1 t2) = t2.
Proof. exact (@lem8135775 _144063 t1 t2). Qed.
Lemma lem8135777 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (a : P) : (term421 _144007 _144038 _144063 P h k f a) = (k f a).
Proof. exact (@lem8135776 _144063 (h f a) (k f a)). Qed.
Lemma lem8135778 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term246 _144007 _144038 _144063 P P' h k f a) = (k f a).
Proof. exact (TRANS (@lem8135773 _144007 _144038 _144063 P h k P' f a h1) (@lem8135777 _144007 _144038 _144063 P h k f a)). Qed.
Lemma lem8135779 {_144063 : Type'} : (@eq _144063) = (@eq _144063).
Proof. exact (eq_refl (@eq _144063)). Qed.
Lemma lem8135780 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term251 _144007 _144038 _144063 P P' h k f a) = (term463 _144007 _144038 _144063 P k f a).
Proof. exact (MK_COMB (@lem8135779 _144063) (@lem8135778 _144007 _144038 _144063 P h k P' f a h1)). Qed.
Lemma lem8135781 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (h g a) = (h g a).
Proof. exact (eq_refl (h g a)). Qed.
Lemma lem8135782 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : ((term246 _144007 _144038 _144063 P P' h k f a) = (h g a)) = ((k f a) = (h g a)).
Proof. exact (MK_COMB (@lem8135780 _144007 _144038 _144063 P h k P' f a h1) (@lem8135781 _144007 _144038 _144063 P h g a)). Qed.
Lemma lem8135785 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term443 _144007 _144038 _144063 P P' k f h g a) = (term477 _144007 _144038 _144063 P k f h g a).
Proof. exact (MK_COMB (@lem8135765 _144007 _144038 _144063 P h g P' f a h1) (@lem8135782 _144007 _144038 _144063 P k h g P' f a h1)). Qed.
Lemma lem8135787 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem8135788 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term477 _144007 _144038 _144063 P k f h g a) = True.
Proof. exact (@lem8135787 ((k f a) = (h g a))). Qed.
Lemma lem8135789 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term443 _144007 _144038 _144063 P P' k f h g a) = True.
Proof. exact (TRANS (@lem8135785 _144007 _144038 _144063 P k h g P' f a h1) (@lem8135788 _144007 _144038 _144063 P k f h g a)). Qed.
Lemma lem8135790 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) : (term367 _144006 _144007 _144038 P lt2 s a f g) = (term367 _144006 _144007 _144038 P lt2 s a f g).
Proof. exact (eq_refl (term367 _144006 _144007 _144038 P lt2 s a f g)). Qed.
Lemma lem8135791 {_144006 _144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term444 _144006 _144007 _144038 _144063 P lt2 s P' k f h g a) = (term465 _144006 _144007 _144038 P lt2 s a f g).
Proof. exact (MK_COMB (@lem8135790 _144006 _144007 _144038 P lt2 s a f g) (@lem8135789 _144007 _144038 _144063 P k h g P' f a h1)). Qed.
Lemma lem8135793 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem8135794 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) : (term465 _144006 _144007 _144038 P lt2 s a f g) = True.
Proof. exact (@lem8135793 (term43 _144006 _144007 _144038 P lt2 s a f g)). Qed.
Lemma lem8135795 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term444 _144006 _144007 _144038 _144063 P lt2 s P' k f h g a) = True.
Proof. exact (TRANS (@lem8135791 _144006 _144007 _144038 _144063 P k h lt2 s g P' f a h1) (@lem8135794 _144006 _144007 _144038 P lt2 s a f g)). Qed.
Lemma lem8135796 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term370 _144007 _144038 P p g a) = (term370 _144007 _144038 P p g a).
Proof. exact (eq_refl (term370 _144007 _144038 P p g a)). Qed.
Lemma lem8135797 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term445 _144006 _144007 _144038 _144063 P p lt2 s P' k f h g a) = (term466 _144007 _144038 P p g a).
Proof. exact (MK_COMB (@lem8135796 _144007 _144038 P p g a) (@lem8135795 _144006 _144007 _144038 _144063 P lt2 s k h g P' f a h1)). Qed.
Lemma lem8135799 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem8135800 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term466 _144007 _144038 P p g a) = True.
Proof. exact (@lem8135799 (p g a)). Qed.
Lemma lem8135801 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term445 _144006 _144007 _144038 _144063 P p lt2 s P' k f h g a) = True.
Proof. exact (TRANS (@lem8135797 _144006 _144007 _144038 _144063 P lt2 s k h p g P' f a h1) (@lem8135800 _144007 _144038 P p g a)). Qed.
Lemma lem8135802 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term370 _144007 _144038 P p f a) = (term370 _144007 _144038 P p f a).
Proof. exact (eq_refl (term370 _144007 _144038 P p f a)). Qed.
Lemma lem8135803 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term446 _144006 _144007 _144038 _144063 P p lt2 s P' k f h g a) = (term466 _144007 _144038 P p f a).
Proof. exact (MK_COMB (@lem8135802 _144007 _144038 P p f a) (@lem8135801 _144006 _144007 _144038 _144063 P p lt2 s k h g P' f a h1)). Qed.
Lemma lem8135805 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem8135806 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term466 _144007 _144038 P p f a) = True.
Proof. exact (@lem8135805 (p f a)). Qed.
Lemma lem8135807 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term446 _144006 _144007 _144038 _144063 P p lt2 s P' k f h g a) = True.
Proof. exact (TRANS (@lem8135803 _144006 _144007 _144038 _144063 P lt2 s k h g p P' f a h1) (@lem8135806 _144007 _144038 P p f a)). Qed.
Lemma lem8135808 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term447 _144006 _144007 _144038 _144063 P lt2 s P' k f h g a) = (term467 _144007 _144038 P).
Proof. exact (fun_ext (fun p : type560 _144007 _144038 P => @lem8135807 _144006 _144007 _144038 _144063 P p lt2 s k h g P' f a h1)). Qed.
Lemma lem8135809 {_144007 _144038 P : Type'} : (@all ((_144007 -> _144038) -> P -> Prop)) = (@all ((_144007 -> _144038) -> P -> Prop)).
Proof. exact (eq_refl (@all ((_144007 -> _144038) -> P -> Prop))). Qed.
Lemma lem8135810 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term448 _144006 _144007 _144038 _144063 P lt2 s P' k f h g a) = (term468 _144007 _144038 P).
Proof. exact (MK_COMB (@lem8135809 _144007 _144038 P) (@lem8135808 _144006 _144007 _144038 _144063 P lt2 s k h g P' f a h1)). Qed.
Lemma lem8135812 {A : Type'} (t : Prop) : (term337 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8135813 {_144007 _144038 P : Type'} (t : Prop) : (term469 _144007 _144038 P t) = t.
Proof. exact (@lem8135812 (type560 _144007 _144038 P) t). Qed.
Lemma lem8135814 {_144007 _144038 P : Type'} : (term468 _144007 _144038 P) = True.
Proof. exact (@lem8135813 _144007 _144038 P True). Qed.
Lemma lem8135815 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term448 _144006 _144007 _144038 _144063 P lt2 s P' k f h g a) = True.
Proof. exact (TRANS (@lem8135810 _144006 _144007 _144038 _144063 P lt2 s k h g P' f a h1) (@lem8135814 _144007 _144038 P)). Qed.
Lemma lem8135816 {_144006 _144007 _144038 _144063 P : Type'} (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term449 _144006 _144007 _144038 _144063 P s P' k f h g a) = (term470 _144006 _144007).
Proof. exact (fun_ext (fun lt2 : type1470 _144006 _144007 => @lem8135815 _144006 _144007 _144038 _144063 P lt2 s k h g P' f a h1)). Qed.
Lemma lem8135817 {_144006 _144007 : Type'} : (@all (_144007 -> _144006 -> Prop)) = (@all (_144007 -> _144006 -> Prop)).
Proof. exact (eq_refl (@all (_144007 -> _144006 -> Prop))). Qed.
Lemma lem8135818 {_144006 _144007 _144038 _144063 P : Type'} (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term450 _144006 _144007 _144038 _144063 P s P' k f h g a) = (term471 _144006 _144007).
Proof. exact (MK_COMB (@lem8135817 _144006 _144007) (@lem8135816 _144006 _144007 _144038 _144063 P s k h g P' f a h1)). Qed.
Lemma lem8135820 {A : Type'} (t : Prop) : (term337 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8135821 {_144006 _144007 : Type'} (t : Prop) : (term472 _144006 _144007 t) = t.
Proof. exact (@lem8135820 (type1470 _144006 _144007) t). Qed.
Lemma lem8135822 {_144006 _144007 : Type'} : (term471 _144006 _144007) = True.
Proof. exact (@lem8135821 _144006 _144007 True). Qed.
Lemma lem8135823 {_144006 _144007 _144038 _144063 P : Type'} (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term450 _144006 _144007 _144038 _144063 P s P' k f h g a) = True.
Proof. exact (TRANS (@lem8135818 _144006 _144007 _144038 _144063 P s k h g P' f a h1) (@lem8135822 _144006 _144007)). Qed.
Lemma lem8135824 {_144006 _144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term451 _144006 _144007 _144038 _144063 P P' k f h g a) = (term473 _144006 P).
Proof. exact (fun_ext (fun s : P -> _144006 => @lem8135823 _144006 _144007 _144038 _144063 P s k h g P' f a h1)). Qed.
Lemma lem8135825 {_144006 P : Type'} : (@all (P -> _144006)) = (@all (P -> _144006)).
Proof. exact (eq_refl (@all (P -> _144006))). Qed.
Lemma lem8135826 {_144006 _144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term452 _144006 _144007 _144038 _144063 P P' k f h g a) = (term474 _144006 P).
Proof. exact (MK_COMB (@lem8135825 _144006 P) (@lem8135824 _144006 _144007 _144038 _144063 P k h g P' f a h1)). Qed.
Lemma lem8135828 {A : Type'} (t : Prop) : (term337 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8135829 {_144006 P : Type'} (t : Prop) : (term475 _144006 P t) = t.
Proof. exact (@lem8135828 (P -> _144006) t). Qed.
Lemma lem8135830 {_144006 P : Type'} : (term474 _144006 P) = True.
Proof. exact (@lem8135829 _144006 P True). Qed.
Lemma lem8135831 {_144006 _144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = False) : (term452 _144006 _144007 _144038 _144063 P P' k f h g a) = True.
Proof. exact (TRANS (@lem8135826 _144006 _144007 _144038 _144063 P k h g P' f a h1) (@lem8135830 _144006 P)). Qed.
Lemma lem8135832 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : term490 _144006 _144007 _144038 _144063 P P' k f h g a.
Proof. exact (fun h0 : (P' f a) = False => @lem8135831 _144006 _144007 _144038 _144063 P k h g P' f a h0). Qed.
Lemma lem8135842 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (P' f a) = True.
Proof. exact (h1). Qed.
Lemma lem8135843 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8135844 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term333 _144007 _144038 P P' f a) = (and True).
Proof. exact (MK_COMB (@lem8135843) (@lem8135842 _144007 _144038 P P' f a h1)). Qed.
Lemma lem8135846 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (P' f a) = True.
Proof. exact (h1). Qed.
Lemma lem8135847 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8135848 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term370 _144007 _144038 P P' f a) = (imp True).
Proof. exact (MK_COMB (@lem8135847) (@lem8135846 _144007 _144038 P P' f a h1)). Qed.
Lemma lem8135851 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : ((h f a) = (h g a)) = ((h f a) = (h g a)).
Proof. exact (eq_refl ((h f a) = (h g a))). Qed.
Lemma lem8135852 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term435 _144007 _144038 _144063 P P' f h g a) = (term460 _144007 _144038 _144063 P f h g a).
Proof. exact (MK_COMB (@lem8135848 _144007 _144038 P P' f a h1) (@lem8135851 _144007 _144038 _144063 P f h g a)). Qed.
Lemma lem8135854 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem8135855 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term460 _144007 _144038 _144063 P f h g a) = ((h f a) = (h g a)).
Proof. exact (@lem8135854 ((h f a) = (h g a))). Qed.
Lemma lem8135858 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term435 _144007 _144038 _144063 P P' f h g a) = ((h f a) = (h g a)).
Proof. exact (TRANS (@lem8135852 _144007 _144038 _144063 P h g P' f a h1) (@lem8135855 _144007 _144038 _144063 P f h g a)). Qed.
Lemma lem8135859 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term439 _144007 _144038 _144063 P P' f h g a) = (term461 _144007 _144038 _144063 P f h g a).
Proof. exact (MK_COMB (@lem8135844 _144007 _144038 P P' f a h1) (@lem8135858 _144007 _144038 _144063 P h g P' f a h1)). Qed.
Lemma lem8135861 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8135862 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term461 _144007 _144038 _144063 P f h g a) = ((h f a) = (h g a)).
Proof. exact (@lem8135861 ((h f a) = (h g a))). Qed.
Lemma lem8135865 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term439 _144007 _144038 _144063 P P' f h g a) = ((h f a) = (h g a)).
Proof. exact (TRANS (@lem8135859 _144007 _144038 _144063 P h g P' f a h1) (@lem8135862 _144007 _144038 _144063 P f h g a)). Qed.
Lemma lem8135866 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8135867 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term440 _144007 _144038 _144063 P P' f h g a) = (term462 _144007 _144038 _144063 P f h g a).
Proof. exact (MK_COMB (@lem8135866) (@lem8135865 _144007 _144038 _144063 P h g P' f a h1)). Qed.
Lemma lem8135869 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (P' f a) = True.
Proof. exact (h1). Qed.
Lemma lem8135870 {_144063 : Type'} : (@COND _144063) = (@COND _144063).
Proof. exact (eq_refl (@COND _144063)). Qed.
Lemma lem8135871 {_144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term418 _144007 _144038 _144063 P P' f a) = (@COND _144063 True).
Proof. exact (MK_COMB (@lem8135870 _144063) (@lem8135869 _144007 _144038 P P' f a h1)). Qed.
Lemma lem8135872 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (a : P) : (h f a) = (h f a).
Proof. exact (eq_refl (h f a)). Qed.
Lemma lem8135873 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term419 _144007 _144038 _144063 P P' h f a) = (term441 _144007 _144038 _144063 P h f a).
Proof. exact (MK_COMB (@lem8135871 _144007 _144038 _144063 P P' f a h1) (@lem8135872 _144007 _144038 _144063 P h f a)). Qed.
Lemma lem8135874 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (a : P) : (k f a) = (k f a).
Proof. exact (eq_refl (k f a)). Qed.
Lemma lem8135875 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term246 _144007 _144038 _144063 P P' h k f a) = (term442 _144007 _144038 _144063 P h k f a).
Proof. exact (MK_COMB (@lem8135873 _144007 _144038 _144063 P h P' f a h1) (@lem8135874 _144007 _144038 _144063 P k f a)). Qed.
Lemma lem8135877 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8135878 {_144063 : Type'} (t2 : _144063) (t1 : _144063) : (@COND _144063 True t1 t2) = t1.
Proof. exact (@lem8135877 _144063 t2 t1). Qed.
Lemma lem8135879 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (a : P) : (term442 _144007 _144038 _144063 P h k f a) = (h f a).
Proof. exact (@lem8135878 _144063 (k f a) (h f a)). Qed.
Lemma lem8135880 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term246 _144007 _144038 _144063 P P' h k f a) = (h f a).
Proof. exact (TRANS (@lem8135875 _144007 _144038 _144063 P h k P' f a h1) (@lem8135879 _144007 _144038 _144063 P k h f a)). Qed.
Lemma lem8135881 {_144063 : Type'} : (@eq _144063) = (@eq _144063).
Proof. exact (eq_refl (@eq _144063)). Qed.
Lemma lem8135882 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term251 _144007 _144038 _144063 P P' h k f a) = (term463 _144007 _144038 _144063 P h f a).
Proof. exact (MK_COMB (@lem8135881 _144063) (@lem8135880 _144007 _144038 _144063 P k h P' f a h1)). Qed.
Lemma lem8135883 {_144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (h g a) = (h g a).
Proof. exact (eq_refl (h g a)). Qed.
Lemma lem8135884 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : ((term246 _144007 _144038 _144063 P P' h k f a) = (h g a)) = ((h f a) = (h g a)).
Proof. exact (MK_COMB (@lem8135882 _144007 _144038 _144063 P k h P' f a h1) (@lem8135883 _144007 _144038 _144063 P h g a)). Qed.
Lemma lem8135887 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term443 _144007 _144038 _144063 P P' k f h g a) = (term464 _144007 _144038 _144063 P f h g a).
Proof. exact (MK_COMB (@lem8135867 _144007 _144038 _144063 P h g P' f a h1) (@lem8135884 _144007 _144038 _144063 P k h g P' f a h1)). Qed.
Lemma lem8135891 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem8135892 {_144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term464 _144007 _144038 _144063 P f h g a) = True.
Proof. exact (@lem8135891 ((h f a) = (h g a))). Qed.
Lemma lem8135893 {_144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term443 _144007 _144038 _144063 P P' k f h g a) = True.
Proof. exact (TRANS (@lem8135887 _144007 _144038 _144063 P k h g P' f a h1) (@lem8135892 _144007 _144038 _144063 P f h g a)). Qed.
Lemma lem8135894 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) : (term367 _144006 _144007 _144038 P lt2 s a f g) = (term367 _144006 _144007 _144038 P lt2 s a f g).
Proof. exact (eq_refl (term367 _144006 _144007 _144038 P lt2 s a f g)). Qed.
Lemma lem8135895 {_144006 _144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term444 _144006 _144007 _144038 _144063 P lt2 s P' k f h g a) = (term465 _144006 _144007 _144038 P lt2 s a f g).
Proof. exact (MK_COMB (@lem8135894 _144006 _144007 _144038 P lt2 s a f g) (@lem8135893 _144007 _144038 _144063 P k h g P' f a h1)). Qed.
Lemma lem8135897 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem8135898 {_144006 _144007 _144038 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) : (term465 _144006 _144007 _144038 P lt2 s a f g) = True.
Proof. exact (@lem8135897 (term43 _144006 _144007 _144038 P lt2 s a f g)). Qed.
Lemma lem8135899 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term444 _144006 _144007 _144038 _144063 P lt2 s P' k f h g a) = True.
Proof. exact (TRANS (@lem8135895 _144006 _144007 _144038 _144063 P k h lt2 s g P' f a h1) (@lem8135898 _144006 _144007 _144038 P lt2 s a f g)). Qed.
Lemma lem8135900 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term370 _144007 _144038 P p g a) = (term370 _144007 _144038 P p g a).
Proof. exact (eq_refl (term370 _144007 _144038 P p g a)). Qed.
Lemma lem8135901 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term445 _144006 _144007 _144038 _144063 P p lt2 s P' k f h g a) = (term466 _144007 _144038 P p g a).
Proof. exact (MK_COMB (@lem8135900 _144007 _144038 P p g a) (@lem8135899 _144006 _144007 _144038 _144063 P lt2 s k h g P' f a h1)). Qed.
Lemma lem8135903 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem8135904 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term466 _144007 _144038 P p g a) = True.
Proof. exact (@lem8135903 (p g a)). Qed.
Lemma lem8135905 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term445 _144006 _144007 _144038 _144063 P p lt2 s P' k f h g a) = True.
Proof. exact (TRANS (@lem8135901 _144006 _144007 _144038 _144063 P lt2 s k h p g P' f a h1) (@lem8135904 _144007 _144038 P p g a)). Qed.
Lemma lem8135906 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term370 _144007 _144038 P p f a) = (term370 _144007 _144038 P p f a).
Proof. exact (eq_refl (term370 _144007 _144038 P p f a)). Qed.
Lemma lem8135907 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term446 _144006 _144007 _144038 _144063 P p lt2 s P' k f h g a) = (term466 _144007 _144038 P p f a).
Proof. exact (MK_COMB (@lem8135906 _144007 _144038 P p f a) (@lem8135905 _144006 _144007 _144038 _144063 P p lt2 s k h g P' f a h1)). Qed.
Lemma lem8135909 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem8135910 {_144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term466 _144007 _144038 P p f a) = True.
Proof. exact (@lem8135909 (p f a)). Qed.
Lemma lem8135911 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term446 _144006 _144007 _144038 _144063 P p lt2 s P' k f h g a) = True.
Proof. exact (TRANS (@lem8135907 _144006 _144007 _144038 _144063 P lt2 s k h g p P' f a h1) (@lem8135910 _144007 _144038 P p f a)). Qed.
Lemma lem8135912 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term447 _144006 _144007 _144038 _144063 P lt2 s P' k f h g a) = (term467 _144007 _144038 P).
Proof. exact (fun_ext (fun p : type560 _144007 _144038 P => @lem8135911 _144006 _144007 _144038 _144063 P p lt2 s k h g P' f a h1)). Qed.
Lemma lem8135913 {_144007 _144038 P : Type'} : (@all ((_144007 -> _144038) -> P -> Prop)) = (@all ((_144007 -> _144038) -> P -> Prop)).
Proof. exact (eq_refl (@all ((_144007 -> _144038) -> P -> Prop))). Qed.
Lemma lem8135914 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term448 _144006 _144007 _144038 _144063 P lt2 s P' k f h g a) = (term468 _144007 _144038 P).
Proof. exact (MK_COMB (@lem8135913 _144007 _144038 P) (@lem8135912 _144006 _144007 _144038 _144063 P lt2 s k h g P' f a h1)). Qed.
Lemma lem8135916 {A : Type'} (t : Prop) : (term337 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8135917 {_144007 _144038 P : Type'} (t : Prop) : (term469 _144007 _144038 P t) = t.
Proof. exact (@lem8135916 (type560 _144007 _144038 P) t). Qed.
Lemma lem8135918 {_144007 _144038 P : Type'} : (term468 _144007 _144038 P) = True.
Proof. exact (@lem8135917 _144007 _144038 P True). Qed.
Lemma lem8135919 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term448 _144006 _144007 _144038 _144063 P lt2 s P' k f h g a) = True.
Proof. exact (TRANS (@lem8135914 _144006 _144007 _144038 _144063 P lt2 s k h g P' f a h1) (@lem8135918 _144007 _144038 P)). Qed.
Lemma lem8135920 {_144006 _144007 _144038 _144063 P : Type'} (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term449 _144006 _144007 _144038 _144063 P s P' k f h g a) = (term470 _144006 _144007).
Proof. exact (fun_ext (fun lt2 : type1470 _144006 _144007 => @lem8135919 _144006 _144007 _144038 _144063 P lt2 s k h g P' f a h1)). Qed.
Lemma lem8135921 {_144006 _144007 : Type'} : (@all (_144007 -> _144006 -> Prop)) = (@all (_144007 -> _144006 -> Prop)).
Proof. exact (eq_refl (@all (_144007 -> _144006 -> Prop))). Qed.
Lemma lem8135922 {_144006 _144007 _144038 _144063 P : Type'} (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term450 _144006 _144007 _144038 _144063 P s P' k f h g a) = (term471 _144006 _144007).
Proof. exact (MK_COMB (@lem8135921 _144006 _144007) (@lem8135920 _144006 _144007 _144038 _144063 P s k h g P' f a h1)). Qed.
Lemma lem8135924 {A : Type'} (t : Prop) : (term337 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8135925 {_144006 _144007 : Type'} (t : Prop) : (term472 _144006 _144007 t) = t.
Proof. exact (@lem8135924 (type1470 _144006 _144007) t). Qed.
Lemma lem8135926 {_144006 _144007 : Type'} : (term471 _144006 _144007) = True.
Proof. exact (@lem8135925 _144006 _144007 True). Qed.
Lemma lem8135927 {_144006 _144007 _144038 _144063 P : Type'} (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term450 _144006 _144007 _144038 _144063 P s P' k f h g a) = True.
Proof. exact (TRANS (@lem8135922 _144006 _144007 _144038 _144063 P s k h g P' f a h1) (@lem8135926 _144006 _144007)). Qed.
Lemma lem8135928 {_144006 _144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term451 _144006 _144007 _144038 _144063 P P' k f h g a) = (term473 _144006 P).
Proof. exact (fun_ext (fun s : P -> _144006 => @lem8135927 _144006 _144007 _144038 _144063 P s k h g P' f a h1)). Qed.
Lemma lem8135929 {_144006 P : Type'} : (@all (P -> _144006)) = (@all (P -> _144006)).
Proof. exact (eq_refl (@all (P -> _144006))). Qed.
Lemma lem8135930 {_144006 _144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term452 _144006 _144007 _144038 _144063 P P' k f h g a) = (term474 _144006 P).
Proof. exact (MK_COMB (@lem8135929 _144006 P) (@lem8135928 _144006 _144007 _144038 _144063 P k h g P' f a h1)). Qed.
Lemma lem8135932 {A : Type'} (t : Prop) : (term337 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8135933 {_144006 P : Type'} (t : Prop) : (term475 _144006 P t) = t.
Proof. exact (@lem8135932 (P -> _144006) t). Qed.
Lemma lem8135934 {_144006 P : Type'} : (term474 _144006 P) = True.
Proof. exact (@lem8135933 _144006 P True). Qed.
Lemma lem8135935 {_144006 _144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : (P' f a) = True) : (term452 _144006 _144007 _144038 _144063 P P' k f h g a) = True.
Proof. exact (TRANS (@lem8135930 _144006 _144007 _144038 _144063 P k h g P' f a h1) (@lem8135934 _144006 P)). Qed.
Lemma lem8135936 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : term491 _144006 _144007 _144038 _144063 P P' k f h g a.
Proof. exact (fun h0 : (P' f a) = True => @lem8135935 _144006 _144007 _144038 _144063 P k h g P' f a h0). Qed.
Lemma lem8135937 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : term492 _144006 _144007 _144038 _144063 P P' k f h g a.
Proof. exact (conj (@lem8135832 _144006 _144007 _144038 _144063 P P' k f h g a) (@lem8135936 _144006 _144007 _144038 _144063 P P' k f h g a)). Qed.
Lemma lem8135939 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term457 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem8135940 {_144006 _144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : term493 _144006 _144007 _144038 _144063 P k h g P' f a.
Proof. exact (@lem8135939 (term452 _144006 _144007 _144038 _144063 P P' k f h g a) True (P' f a) True). Qed.
Lemma lem8135941 {_144006 _144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term452 _144006 _144007 _144038 _144063 P P' k f h g a) = (term481 _144007 _144038 P P' f a).
Proof. exact (@lem8135940 _144006 _144007 _144038 _144063 P k h g P' f a (@lem8135937 _144006 _144007 _144038 _144063 P P' k f h g a)). Qed.
Lemma lem8135943 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem8135944 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term482 _144007 _144038 P P' f a) = True.
Proof. exact (@lem8135943 (P' f a)). Qed.
Lemma lem8135946 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem8135947 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term483 _144007 _144038 P P' f a) = True.
Proof. exact (@lem8135946 (term346 _144007 _144038 P P' f a)). Qed.
Lemma lem8135948 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8135949 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term484 _144007 _144038 P P' f a) = (and True).
Proof. exact (MK_COMB (@lem8135948) (@lem8135947 _144007 _144038 P P' f a)). Qed.
Lemma lem8135950 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term481 _144007 _144038 P P' f a) = (True /\ True).
Proof. exact (MK_COMB (@lem8135949 _144007 _144038 P P' f a) (@lem8135944 _144007 _144038 P P' f a)). Qed.
Lemma lem8135952 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8135953 : (True /\ True) = True.
Proof. exact (@lem8135952 True). Qed.
Lemma lem8135954 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) : (term481 _144007 _144038 P P' f a) = True.
Proof. exact (TRANS (@lem8135950 _144007 _144038 P P' f a) (@lem8135953)). Qed.
Lemma lem8135959 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term452 _144006 _144007 _144038 _144063 P P' k f h g a) = True.
Proof. exact (TRANS (@lem8135941 _144006 _144007 _144038 _144063 P k h g P' f a) (@lem8135954 _144007 _144038 P P' f a)). Qed.
Lemma lem8135960 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term453 _144006 _144007 _144038 _144063 P P' k h g a) = (term485 _144007 _144038).
Proof. exact (fun_ext (fun f : _144007 -> _144038 => @lem8135959 _144006 _144007 _144038 _144063 P P' k f h g a)). Qed.
Lemma lem8135961 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8135962 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term454 _144006 _144007 _144038 _144063 P P' k h g a) = (term486 _144007 _144038).
Proof. exact (MK_COMB (@lem8135961 _144007 _144038) (@lem8135960 _144006 _144007 _144038 _144063 P P' k h g a)). Qed.
Lemma lem8135967 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term494 _144007 _144038 P P' g a) = (term494 _144007 _144038 P P' g a).
Proof. exact (eq_refl (term494 _144007 _144038 P P' g a)). Qed.
Lemma lem8135968 {_144006 _144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term495 _144006 _144007 _144038 _144063 P P' k h g a) = (term496 _144007 _144038 P P' g a).
Proof. exact (MK_COMB (@lem8135967 _144007 _144038 P P' g a) (@lem8135962 _144006 _144007 _144038 _144063 P P' k h g a)). Qed.
Lemma lem8135969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8135970 {_144006 _144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term497 _144006 _144007 _144038 _144063 P P' k h g a) = (term498 _144007 _144038 P P' g a).
Proof. exact (MK_COMB (@lem8135969) (@lem8135968 _144006 _144007 _144038 _144063 P k h P' g a)). Qed.
Lemma lem8135971 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term459 _144006 _144007 _144038 _144063 P P' h k g a) = (term499 _144007 _144038 P P' g a).
Proof. exact (MK_COMB (@lem8135970 _144006 _144007 _144038 _144063 P k h P' g a) (@lem8135732 _144006 _144007 _144038 _144063 P h k P' g a)). Qed.
Lemma lem8135972 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term500 _144006 _144007 _144038 _144063 P P' h k g a) = (term500 _144006 _144007 _144038 _144063 P P' h k g a).
Proof. exact (eq_refl (term500 _144006 _144007 _144038 _144063 P P' h k g a)). Qed.
Lemma lem8135973 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : ((term389 _144006 _144007 _144038 _144063 P P' h k g a) = (term459 _144006 _144007 _144038 _144063 P P' h k g a)) = ((term389 _144006 _144007 _144038 _144063 P P' h k g a) = (term499 _144007 _144038 P P' g a)).
Proof. exact (MK_COMB (@lem8135972 _144006 _144007 _144038 _144063 P P' h k g a) (@lem8135971 _144006 _144007 _144038 _144063 P h k P' g a)). Qed.
Lemma lem8135974 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term389 _144006 _144007 _144038 _144063 P P' h k g a) = (term499 _144007 _144038 P P' g a).
Proof. exact (EQ_MP (@lem8135973 _144006 _144007 _144038 _144063 P h k P' g a) (@lem8135478 _144006 _144007 _144038 _144063 P P' h k g a)). Qed.
Lemma lem8135975 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term391 _144006 _144007 _144038 _144063 P h k g a) = (term501 _144007 _144038 P g a).
Proof. exact (fun_ext (fun P' : type560 _144007 _144038 P => @lem8135974 _144006 _144007 _144038 _144063 P h k P' g a)). Qed.
Lemma lem8135976 {_144007 _144038 P : Type'} : (@all ((_144007 -> _144038) -> P -> Prop)) = (@all ((_144007 -> _144038) -> P -> Prop)).
Proof. exact (eq_refl (@all ((_144007 -> _144038) -> P -> Prop))). Qed.
Lemma lem8135977 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term393 _144006 _144007 _144038 _144063 P h k g a) = (term502 _144007 _144038 P g a).
Proof. exact (MK_COMB (@lem8135976 _144007 _144038 P) (@lem8135975 _144006 _144007 _144038 _144063 P h k g a)). Qed.
Lemma lem8135978 {_144006 _144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term395 _144006 _144007 _144038 _144063 P k g a) = (term503 _144007 _144038 _144063 P g a).
Proof. exact (fun_ext (fun h : type564 _144007 _144038 _144063 P => @lem8135977 _144006 _144007 _144038 _144063 P h k g a)). Qed.
Lemma lem8135979 {_144007 _144038 _144063 P : Type'} : (@all ((_144007 -> _144038) -> P -> _144063)) = (@all ((_144007 -> _144038) -> P -> _144063)).
Proof. exact (eq_refl (@all ((_144007 -> _144038) -> P -> _144063))). Qed.
Lemma lem8135980 {_144006 _144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term397 _144006 _144007 _144038 _144063 P k g a) = (term504 _144007 _144038 _144063 P g a).
Proof. exact (MK_COMB (@lem8135979 _144007 _144038 _144063 P) (@lem8135978 _144006 _144007 _144038 _144063 P k g a)). Qed.
Lemma lem8135981 {_144006 _144007 _144038 _144063 P : Type'} (g : _144007 -> _144038) (a : P) : (term399 _144006 _144007 _144038 _144063 P g a) = (term505 _144007 _144038 _144063 P g a).
Proof. exact (fun_ext (fun k : type564 _144007 _144038 _144063 P => @lem8135980 _144006 _144007 _144038 _144063 P k g a)). Qed.
Lemma lem8135982 {_144007 _144038 _144063 P : Type'} : (@all ((_144007 -> _144038) -> P -> _144063)) = (@all ((_144007 -> _144038) -> P -> _144063)).
Proof. exact (eq_refl (@all ((_144007 -> _144038) -> P -> _144063))). Qed.
Lemma lem8135983 {_144006 _144007 _144038 _144063 P : Type'} (g : _144007 -> _144038) (a : P) : (term401 _144006 _144007 _144038 _144063 P g a) = (term506 _144007 _144038 _144063 P g a).
Proof. exact (MK_COMB (@lem8135982 _144007 _144038 _144063 P) (@lem8135981 _144006 _144007 _144038 _144063 P g a)). Qed.
Lemma lem8135984 {_144006 _144007 _144038 _144063 P : Type'} (a : P) : (term403 _144006 _144007 _144038 _144063 P a) = (term507 _144007 _144038 _144063 P a).
Proof. exact (fun_ext (fun g : _144007 -> _144038 => @lem8135983 _144006 _144007 _144038 _144063 P g a)). Qed.
Lemma lem8135985 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8135986 {_144006 _144007 _144038 _144063 P : Type'} (a : P) : (term405 _144006 _144007 _144038 _144063 P a) = (term508 _144007 _144038 _144063 P a).
Proof. exact (MK_COMB (@lem8135985 _144007 _144038) (@lem8135984 _144006 _144007 _144038 _144063 P a)). Qed.
Lemma lem8135987 {_144006 _144007 _144038 _144063 P : Type'} : (term407 _144006 _144007 _144038 _144063 P) = (term509 _144007 _144038 _144063 P).
Proof. exact (fun_ext (fun a : P => @lem8135986 _144006 _144007 _144038 _144063 P a)). Qed.
Lemma lem8135988 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8135989 {_144006 _144007 _144038 _144063 P : Type'} : (term409 _144006 _144007 _144038 _144063 P) = (term510 _144007 _144038 _144063 P).
Proof. exact (MK_COMB (@lem8135988 P) (@lem8135987 _144006 _144007 _144038 _144063 P)). Qed.
Lemma lem8135990 {_144006 _144007 _144038 _144063 P : Type'} : (term408 _144006 _144007 _144038 _144063 P) = (term510 _144007 _144038 _144063 P).
Proof. exact (TRANS (@lem8135193 _144006 _144007 _144038 _144063 P) (@lem8135989 _144006 _144007 _144038 _144063 P)). Qed.
Lemma lem8136004 {A : Type'} (t : Prop) : (term337 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem8136005 {_144007 _144038 _144063 P : Type'} (t : Prop) : (term511 _144007 _144038 _144063 P t) = t.
Proof. exact (@lem8136004 (type564 _144007 _144038 _144063 P) t). Qed.
Lemma lem8136006 {_144007 _144038 _144063 P : Type'} (g : _144007 -> _144038) (a : P) : (term506 _144007 _144038 _144063 P g a) = (term504 _144007 _144038 _144063 P g a).
Proof. exact (@lem8136005 _144007 _144038 _144063 P (term504 _144007 _144038 _144063 P g a)). Qed.
Lemma lem8136008 {A : Type'} (t : Prop) : (term337 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem8136009 {_144007 _144038 _144063 P : Type'} (t : Prop) : (term511 _144007 _144038 _144063 P t) = t.
Proof. exact (@lem8136008 (type564 _144007 _144038 _144063 P) t). Qed.
Lemma lem8136010 {_144007 _144038 _144063 P : Type'} (g : _144007 -> _144038) (a : P) : (term504 _144007 _144038 _144063 P g a) = (term502 _144007 _144038 P g a).
Proof. exact (@lem8136009 _144007 _144038 _144063 P (term502 _144007 _144038 P g a)). Qed.
Lemma lem8136017 {_144007 _144038 _144063 P : Type'} (g : _144007 -> _144038) (a : P) : (term506 _144007 _144038 _144063 P g a) = (term502 _144007 _144038 P g a).
Proof. exact (TRANS (@lem8136006 _144007 _144038 _144063 P g a) (@lem8136010 _144007 _144038 _144063 P g a)). Qed.
Lemma lem8136023 {A : Type'} (t : Prop) : (term337 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem8136024 {_144007 _144038 : Type'} (t : Prop) : (term512 _144007 _144038 t) = t.
Proof. exact (@lem8136023 (_144007 -> _144038) t). Qed.
Lemma lem8136025 {_144007 _144038 : Type'} : (term486 _144007 _144038) = True.
Proof. exact (@lem8136024 _144007 _144038 True). Qed.
Lemma lem8136026 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term494 _144007 _144038 P P' g a) = (term494 _144007 _144038 P P' g a).
Proof. exact (eq_refl (term494 _144007 _144038 P P' g a)). Qed.
Lemma lem8136027 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term496 _144007 _144038 P P' g a) = (term483 _144007 _144038 P P' g a).
Proof. exact (MK_COMB (@lem8136026 _144007 _144038 P P' g a) (@lem8136025 _144007 _144038)). Qed.
Lemma lem8136029 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem21750 t)). Qed.
Lemma lem8136030 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term483 _144007 _144038 P P' g a) = True.
Proof. exact (@lem8136029 (term346 _144007 _144038 P P' g a)). Qed.
Lemma lem8136031 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term496 _144007 _144038 P P' g a) = True.
Proof. exact (TRANS (@lem8136027 _144007 _144038 P P' g a) (@lem8136030 _144007 _144038 P P' g a)). Qed.
Lemma lem8136032 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8136033 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term498 _144007 _144038 P P' g a) = (and True).
Proof. exact (MK_COMB (@lem8136032) (@lem8136031 _144007 _144038 P P' g a)). Qed.
Lemma lem8136037 {A : Type'} (t : Prop) : (term337 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem8136038 {_144007 _144038 : Type'} (t : Prop) : (term512 _144007 _144038 t) = t.
Proof. exact (@lem8136037 (_144007 -> _144038) t). Qed.
Lemma lem8136039 {_144007 _144038 : Type'} : (term486 _144007 _144038) = True.
Proof. exact (@lem8136038 _144007 _144038 True). Qed.
Lemma lem8136040 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term487 _144007 _144038 P P' g a) = (term487 _144007 _144038 P P' g a).
Proof. exact (eq_refl (term487 _144007 _144038 P P' g a)). Qed.
Lemma lem8136041 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term489 _144007 _144038 P P' g a) = (term482 _144007 _144038 P P' g a).
Proof. exact (MK_COMB (@lem8136040 _144007 _144038 P P' g a) (@lem8136039 _144007 _144038)). Qed.
Lemma lem8136043 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem21750 t)). Qed.
Lemma lem8136044 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term482 _144007 _144038 P P' g a) = True.
Proof. exact (@lem8136043 (P' g a)). Qed.
Lemma lem8136045 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term489 _144007 _144038 P P' g a) = True.
Proof. exact (TRANS (@lem8136041 _144007 _144038 P P' g a) (@lem8136044 _144007 _144038 P P' g a)). Qed.
Lemma lem8136046 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term499 _144007 _144038 P P' g a) = (True /\ True).
Proof. exact (MK_COMB (@lem8136033 _144007 _144038 P P' g a) (@lem8136045 _144007 _144038 P P' g a)). Qed.
Lemma lem8136048 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem21760 t)). Qed.
Lemma lem8136049 : (True /\ True) = True.
Proof. exact (@lem8136048 True). Qed.
Lemma lem8136050 {_144007 _144038 P : Type'} (P' : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) : (term499 _144007 _144038 P P' g a) = True.
Proof. exact (TRANS (@lem8136046 _144007 _144038 P P' g a) (@lem8136049)). Qed.
Lemma lem8136051 {_144007 _144038 P : Type'} (g : _144007 -> _144038) (a : P) : (term501 _144007 _144038 P g a) = (term467 _144007 _144038 P).
Proof. exact (fun_ext (fun P' : type560 _144007 _144038 P => @lem8136050 _144007 _144038 P P' g a)). Qed.
Lemma lem8136052 {_144007 _144038 P : Type'} : (@all ((_144007 -> _144038) -> P -> Prop)) = (@all ((_144007 -> _144038) -> P -> Prop)).
Proof. exact (eq_refl (@all ((_144007 -> _144038) -> P -> Prop))). Qed.
Lemma lem8136053 {_144007 _144038 P : Type'} (g : _144007 -> _144038) (a : P) : (term502 _144007 _144038 P g a) = (term468 _144007 _144038 P).
Proof. exact (MK_COMB (@lem8136052 _144007 _144038 P) (@lem8136051 _144007 _144038 P g a)). Qed.
Lemma lem8136055 {A : Type'} (t : Prop) : (term337 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem8136056 {_144007 _144038 P : Type'} (t : Prop) : (term469 _144007 _144038 P t) = t.
Proof. exact (@lem8136055 (type560 _144007 _144038 P) t). Qed.
Lemma lem8136057 {_144007 _144038 P : Type'} : (term468 _144007 _144038 P) = True.
Proof. exact (@lem8136056 _144007 _144038 P True). Qed.
Lemma lem8136058 {_144007 _144038 P : Type'} (g : _144007 -> _144038) (a : P) : (term502 _144007 _144038 P g a) = True.
Proof. exact (TRANS (@lem8136053 _144007 _144038 P g a) (@lem8136057 _144007 _144038 P)). Qed.
Lemma lem8136059 {_144007 _144038 _144063 P : Type'} (g : _144007 -> _144038) (a : P) : (term506 _144007 _144038 _144063 P g a) = True.
Proof. exact (TRANS (@lem8136017 _144007 _144038 _144063 P g a) (@lem8136058 _144007 _144038 P g a)). Qed.
Lemma lem8136060 {_144007 _144038 _144063 P : Type'} (a : P) : (term507 _144007 _144038 _144063 P a) = (term485 _144007 _144038).
Proof. exact (fun_ext (fun g : _144007 -> _144038 => @lem8136059 _144007 _144038 _144063 P g a)). Qed.
Lemma lem8136061 {_144007 _144038 : Type'} : (@all (_144007 -> _144038)) = (@all (_144007 -> _144038)).
Proof. exact (eq_refl (@all (_144007 -> _144038))). Qed.
Lemma lem8136062 {_144007 _144038 _144063 P : Type'} (a : P) : (term508 _144007 _144038 _144063 P a) = (term486 _144007 _144038).
Proof. exact (MK_COMB (@lem8136061 _144007 _144038) (@lem8136060 _144007 _144038 _144063 P a)). Qed.
Lemma lem8136064 {A : Type'} (t : Prop) : (term337 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem8136065 {_144007 _144038 : Type'} (t : Prop) : (term512 _144007 _144038 t) = t.
Proof. exact (@lem8136064 (_144007 -> _144038) t). Qed.
Lemma lem8136066 {_144007 _144038 : Type'} : (term486 _144007 _144038) = True.
Proof. exact (@lem8136065 _144007 _144038 True). Qed.
Lemma lem8136067 {_144007 _144038 _144063 P : Type'} (a : P) : (term508 _144007 _144038 _144063 P a) = True.
Proof. exact (TRANS (@lem8136062 _144007 _144038 _144063 P a) (@lem8136066 _144007 _144038)). Qed.
Lemma lem8136068 {_144007 _144038 _144063 P : Type'} : (term509 _144007 _144038 _144063 P) = (term335 P).
Proof. exact (fun_ext (fun a : P => @lem8136067 _144007 _144038 _144063 P a)). Qed.
Lemma lem8136069 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8136070 {_144007 _144038 _144063 P : Type'} : (term510 _144007 _144038 _144063 P) = (term336 P).
Proof. exact (MK_COMB (@lem8136069 P) (@lem8136068 _144007 _144038 _144063 P)). Qed.
Lemma lem8136072 {A : Type'} (t : Prop) : (term337 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem8136073 {P : Type'} (t : Prop) : (term337 P t) = t.
Proof. exact (@lem8136072 P t). Qed.
Lemma lem8136074 {P : Type'} : (term336 P) = True.
Proof. exact (@lem8136073 P True). Qed.
Lemma lem8136075 {_144007 _144038 _144063 P : Type'} : (term510 _144007 _144038 _144063 P) = True.
Proof. exact (TRANS (@lem8136070 _144007 _144038 _144063 P) (@lem8136074 P)). Qed.
Lemma lem8136076 {_144006 _144007 _144038 _144063 P : Type'} : (term408 _144006 _144007 _144038 _144063 P) = True.
Proof. exact (TRANS (@lem8135990 _144006 _144007 _144038 _144063 P) (@lem8136075 _144007 _144038 _144063 P)). Qed.
Lemma lem8136077 {_144006 _144007 _144038 _144063 P : Type'} : True = (term408 _144006 _144007 _144038 _144063 P).
Proof. exact (SYM (@lem8136076 _144006 _144007 _144038 _144063 P)). Qed.
Lemma lem8136078 {_144006 _144007 _144038 _144063 P : Type'} : term408 _144006 _144007 _144038 _144063 P.
Proof. exact (EQ_MP (@lem8136077 _144006 _144007 _144038 _144063 P) (@lem0)). Qed.
Lemma lem8136079 {_144006 _144007 _144038 _144063 P : Type'} (a : P) : term513 _144006 _144007 _144038 _144063 P a.
Proof. exact (@lem8136078 _144006 _144007 _144038 _144063 P a). Qed.
Lemma lem8136080 {_144006 _144007 _144038 _144063 P : Type'} (a : P) : (term513 _144006 _144007 _144038 _144063 P a) = (term404 _144006 _144007 _144038 _144063 P a).
Proof. exact (eq_refl (term513 _144006 _144007 _144038 _144063 P a)). Qed.
Lemma lem8136081 {_144006 _144007 _144038 _144063 P : Type'} (a : P) : term404 _144006 _144007 _144038 _144063 P a.
Proof. exact (EQ_MP (@lem8136080 _144006 _144007 _144038 _144063 P a) (@lem8136079 _144006 _144007 _144038 _144063 P a)). Qed.
Lemma lem8136082 {_144006 _144007 _144038 _144063 P : Type'} (a : P) (g : _144007 -> _144038) : term514 _144006 _144007 _144038 _144063 P a g.
Proof. exact (@lem8136081 _144006 _144007 _144038 _144063 P a g). Qed.
Lemma lem8136083 {_144006 _144007 _144038 _144063 P : Type'} (g : _144007 -> _144038) (a : P) : (term514 _144006 _144007 _144038 _144063 P a g) = (term400 _144006 _144007 _144038 _144063 P g a).
Proof. exact (eq_refl (term514 _144006 _144007 _144038 _144063 P a g)). Qed.
Lemma lem8136084 {_144006 _144007 _144038 _144063 P : Type'} (g : _144007 -> _144038) (a : P) : term400 _144006 _144007 _144038 _144063 P g a.
Proof. exact (EQ_MP (@lem8136083 _144006 _144007 _144038 _144063 P g a) (@lem8136082 _144006 _144007 _144038 _144063 P a g)). Qed.
Lemma lem8136085 {_144006 _144007 _144038 _144063 P : Type'} (g : _144007 -> _144038) (a : P) (k : type564 _144007 _144038 _144063 P) : term515 _144006 _144007 _144038 _144063 P g a k.
Proof. exact (@lem8136084 _144006 _144007 _144038 _144063 P g a k). Qed.
Lemma lem8136086 {_144006 _144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term515 _144006 _144007 _144038 _144063 P g a k) = (term396 _144006 _144007 _144038 _144063 P k g a).
Proof. exact (eq_refl (term515 _144006 _144007 _144038 _144063 P g a k)). Qed.
Lemma lem8136087 {_144006 _144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : term396 _144006 _144007 _144038 _144063 P k g a.
Proof. exact (EQ_MP (@lem8136086 _144006 _144007 _144038 _144063 P k g a) (@lem8136085 _144006 _144007 _144038 _144063 P g a k)). Qed.
Lemma lem8136088 {_144006 _144007 _144038 _144063 P : Type'} (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) (h : type564 _144007 _144038 _144063 P) : term516 _144006 _144007 _144038 _144063 P k g a h.
Proof. exact (@lem8136087 _144006 _144007 _144038 _144063 P k g a h). Qed.
Lemma lem8136089 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term516 _144006 _144007 _144038 _144063 P k g a h) = (term392 _144006 _144007 _144038 _144063 P h k g a).
Proof. exact (eq_refl (term516 _144006 _144007 _144038 _144063 P k g a h)). Qed.
Lemma lem8136090 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : term392 _144006 _144007 _144038 _144063 P h k g a.
Proof. exact (EQ_MP (@lem8136089 _144006 _144007 _144038 _144063 P h k g a) (@lem8136088 _144006 _144007 _144038 _144063 P k g a h)). Qed.
Lemma lem8136091 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) (P' : type560 _144007 _144038 P) : term517 _144006 _144007 _144038 _144063 P h k g a P'.
Proof. exact (@lem8136090 _144006 _144007 _144038 _144063 P h k g a P'). Qed.
Lemma lem8136092 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term517 _144006 _144007 _144038 _144063 P h k g a P') = (term388 _144006 _144007 _144038 _144063 P P' h k g a).
Proof. exact (eq_refl (term517 _144006 _144007 _144038 _144063 P h k g a P')). Qed.
Lemma lem8136093 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : term388 _144006 _144007 _144038 _144063 P P' h k g a.
Proof. exact (EQ_MP (@lem8136092 _144006 _144007 _144038 _144063 P P' h k g a) (@lem8136091 _144006 _144007 _144038 _144063 P h k g a P')). Qed.
Lemma lem8136094 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) (f : _144007 -> _144038) : term518 _144006 _144007 _144038 _144063 P P' h k g a f.
Proof. exact (@lem8136093 _144006 _144007 _144038 _144063 P P' h k g a f). Qed.
Lemma lem8136095 {_144006 _144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term518 _144006 _144007 _144038 _144063 P P' h k g a f) = (term384 _144006 _144007 _144038 _144063 P f P' h k g a).
Proof. exact (eq_refl (term518 _144006 _144007 _144038 _144063 P P' h k g a f)). Qed.
Lemma lem8136096 {_144006 _144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : term384 _144006 _144007 _144038 _144063 P f P' h k g a.
Proof. exact (EQ_MP (@lem8136095 _144006 _144007 _144038 _144063 P f P' h k g a) (@lem8136094 _144006 _144007 _144038 _144063 P P' h k g a f)). Qed.
Lemma lem8136097 {_144006 _144007 _144038 _144063 P : Type'} (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) (s : P -> _144006) : term519 _144006 _144007 _144038 _144063 P f P' h k g a s.
Proof. exact (@lem8136096 _144006 _144007 _144038 _144063 P f P' h k g a s). Qed.
Lemma lem8136098 {_144006 _144007 _144038 _144063 P : Type'} (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term519 _144006 _144007 _144038 _144063 P f P' h k g a s) = (term380 _144006 _144007 _144038 _144063 P s f P' h k g a).
Proof. exact (eq_refl (term519 _144006 _144007 _144038 _144063 P f P' h k g a s)). Qed.
Lemma lem8136099 {_144006 _144007 _144038 _144063 P : Type'} (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : term380 _144006 _144007 _144038 _144063 P s f P' h k g a.
Proof. exact (EQ_MP (@lem8136098 _144006 _144007 _144038 _144063 P s f P' h k g a) (@lem8136097 _144006 _144007 _144038 _144063 P f P' h k g a s)). Qed.
Lemma lem8136100 {_144006 _144007 _144038 _144063 P : Type'} (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) (lt2 : type1470 _144006 _144007) : term520 _144006 _144007 _144038 _144063 P s f P' h k g a lt2.
Proof. exact (@lem8136099 _144006 _144007 _144038 _144063 P s f P' h k g a lt2). Qed.
Lemma lem8136101 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term520 _144006 _144007 _144038 _144063 P s f P' h k g a lt2) = (term376 _144006 _144007 _144038 _144063 P lt2 s f P' h k g a).
Proof. exact (eq_refl (term520 _144006 _144007 _144038 _144063 P s f P' h k g a lt2)). Qed.
Lemma lem8136102 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : term376 _144006 _144007 _144038 _144063 P lt2 s f P' h k g a.
Proof. exact (EQ_MP (@lem8136101 _144006 _144007 _144038 _144063 P lt2 s f P' h k g a) (@lem8136100 _144006 _144007 _144038 _144063 P s f P' h k g a lt2)). Qed.
Lemma lem8136103 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) (p : type560 _144007 _144038 P) : term521 _144006 _144007 _144038 _144063 P lt2 s f P' h k g a p.
Proof. exact (@lem8136102 _144006 _144007 _144038 _144063 P lt2 s f P' h k g a p). Qed.
Lemma lem8136104 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : (term521 _144006 _144007 _144038 _144063 P lt2 s f P' h k g a p) = (term361 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a).
Proof. exact (eq_refl (term521 _144006 _144007 _144038 _144063 P lt2 s f P' h k g a p)). Qed.
Lemma lem8136105 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : term361 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a.
Proof. exact (EQ_MP (@lem8136104 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a) (@lem8136103 _144006 _144007 _144038 _144063 P lt2 s f P' h k g a p)). Qed.
Lemma lem8136107 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : term361 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a.
Proof. exact (@lem8135045 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a (@lem8136105 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a)). Qed.
Lemma lem8136108 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : p f a) : term371 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a.
Proof. exact (@lem8136107 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a (@lem8134807 _144007 _144038 P p f a h1)). Qed.
Lemma lem8136109 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : p f a) (h2 : p g a) : term368 _144006 _144007 _144038 _144063 P lt2 s f P' h k g a.
Proof. exact (@lem8136108 _144006 _144007 _144038 _144063 P lt2 s P' h k g p f a h1 (@lem8134809 _144007 _144038 P p g a h2)). Qed.
Lemma lem8136110 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : p f a) (h3 : p g a) : term359 _144007 _144038 _144063 P f P' h k g a.
Proof. exact (@lem8136109 _144006 _144007 _144038 _144063 P lt2 s P' h k f p g a h2 h3 (@lem8134808 _144006 _144007 _144038 P lt2 s a f g h1)). Qed.
Lemma lem8136111 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : term360 _144007 _144038 _144063 P f P' h k g a) (h3 : p f a) (h4 : p g a) : False.
Proof. exact (@lem8136110 _144006 _144007 _144038 _144063 P P' h k lt2 s f p g a h1 h3 h4 (@lem8135029 _144007 _144038 _144063 P f P' h k g a h2)). Qed.
Lemma lem8136112 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : term360 _144007 _144038 _144063 P f P' h k g a) (h3 : p f a) (h4 : p g a) : (term360 _144007 _144038 _144063 P f P' h k g a) = False.
Proof. exact (prop_ext (fun h5 : term360 _144007 _144038 _144063 P f P' h k g a => @lem8136111 _144006 _144007 _144038 _144063 P lt2 s P' h k f p g a h1 h2 h3 h4) (fun h5 : False => @lem8135029 _144007 _144038 _144063 P f P' h k g a h2)). Qed.
Lemma lem8136113 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (s : P -> _144006) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : term360 _144007 _144038 _144063 P f P' h k g a) (h3 : p f a) (h4 : p g a) : False.
Proof. exact (EQ_MP (@lem8136112 _144006 _144007 _144038 _144063 P lt2 s P' h k f p g a h1 h2 h3 h4) (@lem8135029 _144007 _144038 _144063 P f P' h k g a h2)). Qed.
Lemma lem8136114 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : p f a) (h3 : p g a) : term359 _144007 _144038 _144063 P f P' h k g a.
Proof. exact (fun h0 : term360 _144007 _144038 _144063 P f P' h k g a => @lem8136113 _144006 _144007 _144038 _144063 P lt2 s P' h k f p g a h1 h0 h2 h3). Qed.
Lemma lem8136115 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : p f a) (h3 : p g a) : term357 _144007 _144038 _144063 P f P' h k g a.
Proof. exact (EQ_MP (@lem8135028 _144007 _144038 _144063 P f P' h k g a) (@lem8136114 _144006 _144007 _144038 _144063 P P' h k lt2 s f p g a h1 h2 h3)). Qed.
Lemma lem8136116 {_144006 _144007 _144038 _144063 P : Type'} (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : p f a) (h3 : p g a) : term356 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a.
Proof. exact (EQ_MP (@lem8135024 _144006 _144007 _144038 _144063 P P' h k lt2 s f p g a h1 h2 h3) (@lem8136115 _144006 _144007 _144038 _144063 P P' h k lt2 s f p g a h1 h2 h3)). Qed.
Lemma lem8136117 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : term222 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a) (h3 : p f a) (h4 : p g a) : (term246 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k g a).
Proof. exact (@lem8136116 _144006 _144007 _144038 _144063 P P' h k lt2 s f p g a h1 h3 h4 (@lem8134804 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a h2)). Qed.
Lemma lem8136118 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) (h1 : term329 _144006 _144007 _144038 P p lt2 s a f g) : term330 _144006 _144007 _144038 P p lt2 s a f g.
Proof. exact (proj2 (@lem8134805 _144006 _144007 _144038 P p lt2 s a f g h1)). Qed.
Lemma lem8136119 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) (h1 : term329 _144006 _144007 _144038 P p lt2 s a f g) : p f a.
Proof. exact (proj1 (@lem8134805 _144006 _144007 _144038 P p lt2 s a f g h1)). Qed.
Lemma lem8136120 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) (h1 : term330 _144006 _144007 _144038 P p lt2 s a f g) : term43 _144006 _144007 _144038 P lt2 s a f g.
Proof. exact (proj2 (@lem8134806 _144006 _144007 _144038 P p lt2 s a f g h1)). Qed.
Lemma lem8136121 {_144006 _144007 _144038 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) (h1 : term330 _144006 _144007 _144038 P p lt2 s a f g) : p g a.
Proof. exact (proj1 (@lem8134806 _144006 _144007 _144038 P p lt2 s a f g h1)). Qed.
Lemma lem8136122 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : term222 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a) (h3 : p f a) (h4 : p g a) : (term43 _144006 _144007 _144038 P lt2 s a f g) = ((term246 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k g a)).
Proof. exact (prop_ext (fun h5 : term43 _144006 _144007 _144038 P lt2 s a f g => @lem8136117 _144006 _144007 _144038 _144063 P h P' lt2 s k f p g a h1 h2 h3 h4) (fun h5 : (term246 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k g a) => @lem8134808 _144006 _144007 _144038 P lt2 s a f g h1)). Qed.
Lemma lem8136123 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : term222 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a) (h3 : p f a) (h4 : p g a) : (term246 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k g a).
Proof. exact (EQ_MP (@lem8136122 _144006 _144007 _144038 _144063 P h P' lt2 s k f p g a h1 h2 h3 h4) (@lem8134808 _144006 _144007 _144038 P lt2 s a f g h1)). Qed.
Lemma lem8136124 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : term222 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a) (h3 : p f a) (h4 : p g a) : (p g a) = ((term246 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k g a)).
Proof. exact (prop_ext (fun h5 : p g a => @lem8136123 _144006 _144007 _144038 _144063 P h P' lt2 s k f p g a h1 h2 h3 h4) (fun h5 : (term246 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k g a) => @lem8134809 _144007 _144038 P p g a h4)). Qed.
Lemma lem8136125 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (k : type564 _144007 _144038 _144063 P) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term43 _144006 _144007 _144038 P lt2 s a f g) (h2 : term222 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a) (h3 : p f a) (h4 : p g a) : (term246 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k g a).
Proof. exact (EQ_MP (@lem8136124 _144006 _144007 _144038 _144063 P h P' lt2 s k f p g a h1 h2 h3 h4) (@lem8134809 _144007 _144038 P p g a h4)). Qed.
Lemma lem8136126 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (k : type564 _144007 _144038 _144063 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term222 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a) (h2 : term330 _144006 _144007 _144038 P p lt2 s a f g) (h3 : p f a) (h4 : p g a) : (term43 _144006 _144007 _144038 P lt2 s a f g) = ((term246 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k g a)).
Proof. exact (prop_ext (fun h5 : term43 _144006 _144007 _144038 P lt2 s a f g => @lem8136125 _144006 _144007 _144038 _144063 P h P' lt2 s k f p g a h5 h1 h3 h4) (fun h5 : (term246 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k g a) => @lem8136120 _144006 _144007 _144038 P p lt2 s a f g h2)). Qed.
Lemma lem8136127 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (k : type564 _144007 _144038 _144063 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (p : type560 _144007 _144038 P) (g : _144007 -> _144038) (a : P) (h1 : term222 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a) (h2 : term330 _144006 _144007 _144038 P p lt2 s a f g) (h3 : p f a) (h4 : p g a) : (term246 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k g a).
Proof. exact (EQ_MP (@lem8136126 _144006 _144007 _144038 _144063 P h P' k lt2 s f p g a h1 h2 h3 h4) (@lem8136120 _144006 _144007 _144038 P p lt2 s a f g h2)). Qed.
Lemma lem8136128 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (k : type564 _144007 _144038 _144063 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (g : _144007 -> _144038) (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : term222 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a) (h2 : term330 _144006 _144007 _144038 P p lt2 s a f g) (h3 : p f a) : (p g a) = ((term246 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k g a)).
Proof. exact (prop_ext (fun h4 : p g a => @lem8136127 _144006 _144007 _144038 _144063 P h P' k lt2 s f p g a h1 h2 h3 h4) (fun h4 : (term246 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k g a) => @lem8136121 _144006 _144007 _144038 P p lt2 s a f g h2)). Qed.
Lemma lem8136129 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (k : type564 _144007 _144038 _144063 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (g : _144007 -> _144038) (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : term222 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a) (h2 : term330 _144006 _144007 _144038 P p lt2 s a f g) (h3 : p f a) : (term246 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k g a).
Proof. exact (EQ_MP (@lem8136128 _144006 _144007 _144038 _144063 P h P' k lt2 s g p f a h1 h2 h3) (@lem8136121 _144006 _144007 _144038 P p lt2 s a f g h2)). Qed.
Lemma lem8136130 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (k : type564 _144007 _144038 _144063 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (g : _144007 -> _144038) (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : term222 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a) (h2 : term330 _144006 _144007 _144038 P p lt2 s a f g) (h3 : p f a) : (p f a) = ((term246 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k g a)).
Proof. exact (prop_ext (fun h4 : p f a => @lem8136129 _144006 _144007 _144038 _144063 P h P' k lt2 s g p f a h1 h2 h3) (fun h4 : (term246 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k g a) => @lem8134807 _144007 _144038 P p f a h3)). Qed.
Lemma lem8136131 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (k : type564 _144007 _144038 _144063 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (g : _144007 -> _144038) (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : term222 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a) (h2 : term330 _144006 _144007 _144038 P p lt2 s a f g) (h3 : p f a) : (term246 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k g a).
Proof. exact (EQ_MP (@lem8136130 _144006 _144007 _144038 _144063 P h P' k lt2 s g p f a h1 h2 h3) (@lem8134807 _144007 _144038 P p f a h3)). Qed.
Lemma lem8136132 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (k : type564 _144007 _144038 _144063 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (g : _144007 -> _144038) (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : term222 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a) (h2 : term329 _144006 _144007 _144038 P p lt2 s a f g) (h3 : p f a) : (term330 _144006 _144007 _144038 P p lt2 s a f g) = ((term246 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k g a)).
Proof. exact (prop_ext (fun h4 : term330 _144006 _144007 _144038 P p lt2 s a f g => @lem8136131 _144006 _144007 _144038 _144063 P h P' k lt2 s g p f a h1 h4 h3) (fun h4 : (term246 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k g a) => @lem8136118 _144006 _144007 _144038 P p lt2 s a f g h2)). Qed.
Lemma lem8136133 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (k : type564 _144007 _144038 _144063 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (g : _144007 -> _144038) (p : type560 _144007 _144038 P) (f : _144007 -> _144038) (a : P) (h1 : term222 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a) (h2 : term329 _144006 _144007 _144038 P p lt2 s a f g) (h3 : p f a) : (term246 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k g a).
Proof. exact (EQ_MP (@lem8136132 _144006 _144007 _144038 _144063 P h P' k lt2 s g p f a h1 h2 h3) (@lem8136118 _144006 _144007 _144038 P p lt2 s a f g h2)). Qed.
Lemma lem8136134 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (k : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) (h1 : term222 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a) (h2 : term329 _144006 _144007 _144038 P p lt2 s a f g) : (p f a) = ((term246 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k g a)).
Proof. exact (prop_ext (fun h3 : p f a => @lem8136133 _144006 _144007 _144038 _144063 P h P' k lt2 s g p f a h1 h2 h3) (fun h3 : (term246 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k g a) => @lem8136119 _144006 _144007 _144038 P p lt2 s a f g h2)). Qed.
Lemma lem8136135 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (P' : type560 _144007 _144038 P) (k : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (a : P) (f : _144007 -> _144038) (g : _144007 -> _144038) (h1 : term222 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a) (h2 : term329 _144006 _144007 _144038 P p lt2 s a f g) : (term246 _144007 _144038 _144063 P P' h k f a) = (term246 _144007 _144038 _144063 P P' h k g a).
Proof. exact (EQ_MP (@lem8136134 _144006 _144007 _144038 _144063 P h P' k p lt2 s a f g h1 h2) (@lem8136119 _144006 _144007 _144038 P p lt2 s a f g h2)). Qed.
Lemma lem8136136 {_144006 _144007 _144038 _144063 P : Type'} (h : type564 _144007 _144038 _144063 P) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) (h1 : term222 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a) : term254 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a.
Proof. exact (fun h0 : term329 _144006 _144007 _144038 P p lt2 s a f g => @lem8136135 _144006 _144007 _144038 _144063 P h P' k p lt2 s a f g h1 h0). Qed.
Lemma lem8136137 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) (a : P) : term315 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a.
Proof. exact (fun h0 : term222 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a => @lem8136136 _144006 _144007 _144038 _144063 P h p P' lt2 s f k g a h0). Qed.
Lemma lem8136142 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : term319 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g.
Proof. exact (fun a : P => @lem8136137 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g a). Qed.
Lemma lem8136143 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) (g : _144007 -> _144038) : term295 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g.
Proof. exact (@lem8134801 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g (@lem8136142 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g)). Qed.
Lemma lem8136148 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : term299 _144006 _144007 _144038 _144063 P p lt2 s f P' h k.
Proof. exact (fun g : _144007 -> _144038 => @lem8136143 _144006 _144007 _144038 _144063 P p lt2 s f P' h k g). Qed.
Lemma lem8136149 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (f : _144007 -> _144038) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : term275 _144006 _144007 _144038 _144063 P p lt2 s f P' h k.
Proof. exact (@lem8134774 _144006 _144007 _144038 _144063 P p lt2 s f P' h k (@lem8136148 _144006 _144007 _144038 _144063 P p lt2 s f P' h k)). Qed.
Lemma lem8136154 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : term279 _144006 _144007 _144038 _144063 P p lt2 s P' h k.
Proof. exact (fun f : _144007 -> _144038 => @lem8136149 _144006 _144007 _144038 _144063 P p lt2 s f P' h k). Qed.
Lemma lem8136155 {_144006 _144007 _144038 _144063 P : Type'} (p : type560 _144007 _144038 P) (lt2 : type1470 _144006 _144007) (s : P -> _144006) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : term267 _144006 _144007 _144038 _144063 P p lt2 s P' h k.
Proof. exact (@lem8134747 _144006 _144007 _144038 _144063 P p lt2 s P' h k (@lem8136154 _144006 _144007 _144038 _144063 P p lt2 s P' h k)). Qed.
Lemma lem8136156 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (p : type560 _144007 _144038 P) (s : P -> _144006) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) (k : type564 _144007 _144038 _144063 P) : term266 _144006 _144007 _144038 _144063 P lt2 p s P' h k.
Proof. exact (EQ_MP (@lem8134720 _144006 _144007 _144038 _144063 P lt2 p s P' h k) (@lem8136155 _144006 _144007 _144038 _144063 P p lt2 s P' h k)). Qed.
Lemma lem8136161 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (p : type560 _144007 _144038 P) (s : P -> _144006) (P' : type560 _144007 _144038 P) (h : type564 _144007 _144038 _144063 P) : term522 _144006 _144007 _144038 _144063 P lt2 p s P' h.
Proof. exact (fun k : type564 _144007 _144038 _144063 P => @lem8136156 _144006 _144007 _144038 _144063 P lt2 p s P' h k). Qed.
Lemma lem8136166 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (p : type560 _144007 _144038 P) (s : P -> _144006) (P' : type560 _144007 _144038 P) : term523 _144006 _144007 _144038 _144063 P lt2 p s P'.
Proof. exact (fun h : type564 _144007 _144038 _144063 P => @lem8136161 _144006 _144007 _144038 _144063 P lt2 p s P' h). Qed.
Lemma lem8136171 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (p : type560 _144007 _144038 P) (P' : type560 _144007 _144038 P) : term524 _144006 _144007 _144038 _144063 P lt2 p P'.
Proof. exact (fun s : P -> _144006 => @lem8136166 _144006 _144007 _144038 _144063 P lt2 p s P'). Qed.
Lemma lem8136176 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) (p : type560 _144007 _144038 P) : term525 _144006 _144007 _144038 _144063 P lt2 p.
Proof. exact (fun P' : type560 _144007 _144038 P => @lem8136171 _144006 _144007 _144038 _144063 P lt2 p P'). Qed.
Lemma lem8136181 {_144006 _144007 _144038 _144063 P : Type'} (lt2 : type1470 _144006 _144007) : term526 _144006 _144007 _144038 _144063 P lt2.
Proof. exact (fun p : type560 _144007 _144038 P => @lem8136176 _144006 _144007 _144038 _144063 P lt2 p). Qed.
Lemma lem8136186 {_144006 _144007 _144038 _144063 P : Type'} : term527 _144006 _144007 _144038 _144063 P.
Proof. exact (fun lt2 : type1470 _144006 _144007 => @lem8136181 _144006 _144007 _144038 _144063 P lt2). Qed.
