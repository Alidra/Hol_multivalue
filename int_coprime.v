Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_coprime_term_abbrevs.
Require Import FST_spec.
Require Import SND_spec.
Lemma lem2443954 : int_coprime = term0.
Proof. exact (@int_coprime_def). Qed.
Lemma lem2443955 (_29564 : prod int int) : _29564 = _29564.
Proof. exact (eq_refl _29564). Qed.
Lemma lem2443956 (_29564 : prod int int) : (int_coprime _29564) = (term1 _29564).
Proof. exact (MK_COMB (@lem2443954) (@lem2443955 _29564)). Qed.
Lemma lem2443957 (_29564 : prod int int) : (term1 _29564) = (term2 _29564).
Proof. exact (eq_refl (term1 _29564)). Qed.
Lemma lem2443958 (_29564 : prod int int) : (int_coprime _29564) = (term2 _29564).
Proof. exact (TRANS (@lem2443956 _29564) (@lem2443957 _29564)). Qed.
Lemma lem2443959 : term3.
Proof. exact (fun _29564 : prod int int => @lem2443958 _29564). Qed.
Lemma lem2443960 (_29564 : prod int int) : term4 _29564.
Proof. exact (@lem2443959 _29564). Qed.
Lemma lem2443961 (_29564 : prod int int) : (term4 _29564) = ((int_coprime _29564) = (term2 _29564)).
Proof. exact (eq_refl (term4 _29564)). Qed.
Lemma lem2443962 (_29564 : prod int int) : (int_coprime _29564) = (term2 _29564).
Proof. exact (EQ_MP (@lem2443961 _29564) (@lem2443960 _29564)). Qed.
Lemma lem2443963 (a : int) (b : int) : (term5 a b) = (term6 a b).
Proof. exact (@lem2443962 (@pair int int a b)). Qed.
Lemma lem2443964 {A B : Type'} (x : A) : term7 A B x.
Proof. exact (@lem48019 A B x). Qed.
Lemma lem2443965 {A B : Type'} (x : A) : (term7 A B x) = (term8 A B x).
Proof. exact (eq_refl (term7 A B x)). Qed.
Lemma lem2443966 {A B : Type'} (x : A) : term8 A B x.
Proof. exact (EQ_MP (@lem2443965 A B x) (@lem2443964 A B x)). Qed.
Lemma lem2443967 {A B : Type'} (x : A) (y : B) : term9 A B x y.
Proof. exact (@lem2443966 A B x y). Qed.
Lemma lem2443968 {A B : Type'} (x : A) (y : B) : (term9 A B x y) = ((term10 A B x y) = y).
Proof. exact (eq_refl (term9 A B x y)). Qed.
Lemma lem2443970 {A B : Type'} (x : A) : term11 A B x.
Proof. exact (@lem47827 A B x). Qed.
Lemma lem2443971 {A B : Type'} (x : A) : (term11 A B x) = (term12 A B x).
Proof. exact (eq_refl (term11 A B x)). Qed.
Lemma lem2443972 {A B : Type'} (x : A) : term12 A B x.
Proof. exact (EQ_MP (@lem2443971 A B x) (@lem2443970 A B x)). Qed.
Lemma lem2443973 {A B : Type'} (x : A) (y : B) : term13 A B x y.
Proof. exact (@lem2443972 A B x y). Qed.
Lemma lem2443974 {A B : Type'} (y : B) (x : A) : (term13 A B x y) = ((term14 A B x y) = x).
Proof. exact (eq_refl (term13 A B x y)). Qed.
Lemma lem2443977 {A B : Type'} (y : B) (x : A) : (term14 A B x y) = x.
Proof. exact (EQ_MP (@lem2443974 A B y x) (@lem2443973 A B x y)). Qed.
Lemma lem2443978 (y : int) (x : int) : (term15 x y) = x.
Proof. exact (@lem2443977 int int y x). Qed.
Lemma lem2443979 (b : int) (a : int) : (term15 a b) = a.
Proof. exact (@lem2443978 b a). Qed.
Lemma lem2443980 (a : int) (b : int) : a = (term15 a b).
Proof. exact (SYM (@lem2443979 b a)). Qed.
Lemma lem2443982 {A B : Type'} (x : A) (y : B) : (term10 A B x y) = y.
Proof. exact (EQ_MP (@lem2443968 A B x y) (@lem2443967 A B x y)). Qed.
Lemma lem2443983 (x : int) (y : int) : (term16 x y) = y.
Proof. exact (@lem2443982 int int x y). Qed.
Lemma lem2443984 (a : int) (b : int) : (term16 a b) = b.
Proof. exact (@lem2443983 a b). Qed.
Lemma lem2443985 (a : int) (b : int) : b = (term16 a b).
Proof. exact (SYM (@lem2443984 a b)). Qed.
Lemma lem2443986 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem2443987 (a : int) (b : int) : (term18 a) = (term19 a b).
Proof. exact (MK_COMB (@lem2443986) (@lem2443980 a b)). Qed.
Lemma lem2443988 (a : int) (b : int) : (term19 a b) = (term20 a b).
Proof. exact (eq_refl (term19 a b)). Qed.
Lemma lem2443989 (a : int) : (term21 a) = (term21 a).
Proof. exact (eq_refl (term21 a)). Qed.
Lemma lem2443990 (a : int) (b : int) : ((term18 a) = (term19 a b)) = ((term18 a) = (term20 a b)).
Proof. exact (MK_COMB (@lem2443989 a) (@lem2443988 a b)). Qed.
Lemma lem2443991 (a : int) : (term18 a) = (term22 a).
Proof. exact (eq_refl (term18 a)). Qed.
Lemma lem2443992 : (@eq (int -> Prop)) = (@eq (int -> Prop)).
Proof. exact (eq_refl (@eq (int -> Prop))). Qed.
Lemma lem2443993 (a : int) : (term21 a) = (term23 a).
Proof. exact (MK_COMB (@lem2443992) (@lem2443991 a)). Qed.
Lemma lem2443994 (a : int) (b : int) : (term20 a b) = (term20 a b).
Proof. exact (eq_refl (term20 a b)). Qed.
Lemma lem2443995 (a : int) (b : int) : ((term18 a) = (term20 a b)) = ((term22 a) = (term20 a b)).
Proof. exact (MK_COMB (@lem2443993 a) (@lem2443994 a b)). Qed.
Lemma lem2443996 (a : int) (b : int) : ((term18 a) = (term19 a b)) = ((term22 a) = (term20 a b)).
Proof. exact (TRANS (@lem2443990 a b) (@lem2443995 a b)). Qed.
Lemma lem2443997 (a : int) (b : int) : (term22 a) = (term20 a b).
Proof. exact (EQ_MP (@lem2443996 a b) (@lem2443987 a b)). Qed.
Lemma lem2443998 (a : int) (b : int) : (term24 a b) = (term25 a b).
Proof. exact (MK_COMB (@lem2443997 a b) (@lem2443985 a b)). Qed.
Lemma lem2443999 (a : int) (b : int) : (term25 a b) = (term6 a b).
Proof. exact (eq_refl (term25 a b)). Qed.
Lemma lem2444000 (a : int) (b : int) : (term26 a b) = (term26 a b).
Proof. exact (eq_refl (term26 a b)). Qed.
Lemma lem2444001 (a : int) (b : int) : ((term24 a b) = (term25 a b)) = ((term24 a b) = (term6 a b)).
Proof. exact (MK_COMB (@lem2444000 a b) (@lem2443999 a b)). Qed.
Lemma lem2444002 (a : int) (b : int) : (term24 a b) = (term27 a b).
Proof. exact (eq_refl (term24 a b)). Qed.
Lemma lem2444003 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2444004 (a : int) (b : int) : (term26 a b) = (term28 a b).
Proof. exact (MK_COMB (@lem2444003) (@lem2444002 a b)). Qed.
Lemma lem2444005 (a : int) (b : int) : (term6 a b) = (term6 a b).
Proof. exact (eq_refl (term6 a b)). Qed.
Lemma lem2444006 (a : int) (b : int) : ((term24 a b) = (term6 a b)) = ((term27 a b) = (term6 a b)).
Proof. exact (MK_COMB (@lem2444004 a b) (@lem2444005 a b)). Qed.
Lemma lem2444007 (a : int) (b : int) : ((term24 a b) = (term25 a b)) = ((term27 a b) = (term6 a b)).
Proof. exact (TRANS (@lem2444001 a b) (@lem2444006 a b)). Qed.
Lemma lem2444008 (a : int) (b : int) : (term27 a b) = (term6 a b).
Proof. exact (EQ_MP (@lem2444007 a b) (@lem2443998 a b)). Qed.
Lemma lem2444009 (a : int) (b : int) : (term6 a b) = (term27 a b).
Proof. exact (SYM (@lem2444008 a b)). Qed.
Lemma lem2444010 (a : int) (b : int) : (term5 a b) = (term27 a b).
Proof. exact (TRANS (@lem2443963 a b) (@lem2444009 a b)). Qed.
Lemma lem2444011 (a : int) : term29 a.
Proof. exact (fun b : int => @lem2444010 a b). Qed.
Lemma lem2444012 : term30.
Proof. exact (fun a : int => @lem2444011 a). Qed.
