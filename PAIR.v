Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PAIR_term_abbrevs.
Require Import FST_spec.
Require Import PAIR_SURJECTIVE_spec.
Require Import SND_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem48020 {A B : Type'} (x : A) : term0 A B x.
Proof. exact (@lem48019 A B x). Qed.
Lemma lem48021 {A B : Type'} (x : A) : (term0 A B x) = (term1 A B x).
Proof. exact (eq_refl (term0 A B x)). Qed.
Lemma lem48022 {A B : Type'} (x : A) : term1 A B x.
Proof. exact (EQ_MP (@lem48021 A B x) (@lem48020 A B x)). Qed.
Lemma lem48023 {A B : Type'} (x : A) (y : B) : term2 A B x y.
Proof. exact (@lem48022 A B x y). Qed.
Lemma lem48024 {A B : Type'} (x : A) (y : B) : (term2 A B x y) = ((term3 A B x y) = y).
Proof. exact (eq_refl (term2 A B x y)). Qed.
Lemma lem48026 {A B : Type'} (x : A) : term4 A B x.
Proof. exact (@lem47827 A B x). Qed.
Lemma lem48027 {A B : Type'} (x : A) : (term4 A B x) = (term5 A B x).
Proof. exact (eq_refl (term4 A B x)). Qed.
Lemma lem48028 {A B : Type'} (x : A) : term5 A B x.
Proof. exact (EQ_MP (@lem48027 A B x) (@lem48026 A B x)). Qed.
Lemma lem48029 {A B : Type'} (x : A) (y : B) : term6 A B x y.
Proof. exact (@lem48028 A B x y). Qed.
Lemma lem48030 {A B : Type'} (y : B) (x : A) : (term6 A B x y) = ((term7 A B x y) = x).
Proof. exact (eq_refl (term6 A B x y)). Qed.
Lemma lem48032 {A B : Type'} (x : prod A B) : term8 A B x.
Proof. exact (@lem47629 A B x). Qed.
Lemma lem48033 {A B : Type'} (x : prod A B) : (term8 A B x) = (term9 A B x).
Proof. exact (eq_refl (term8 A B x)). Qed.
Lemma lem48034 {A B : Type'} (x : prod A B) : term9 A B x.
Proof. exact (EQ_MP (@lem48033 A B x) (@lem48032 A B x)). Qed.
Lemma lem48035 {A B : Type'} (x : prod A B) (a : A) (h1 : term10 A B x a) : term10 A B x a.
Proof. exact (h1). Qed.
Lemma lem48036 {A B : Type'} (x : prod A B) (a : A) (b : B) (h1 : x = (@pair A B a b)) : x = (@pair A B a b).
Proof. exact (h1). Qed.
Lemma lem48037 {A B : Type'} : (term11 A B) = (term11 A B).
Proof. exact (eq_refl (term11 A B)). Qed.
Lemma lem48038 {A B : Type'} (x : prod A B) (a : A) (b : B) (h1 : x = (@pair A B a b)) : (term12 A B x) = (term13 A B a b).
Proof. exact (MK_COMB (@lem48037 A B) (@lem48036 A B x a b h1)). Qed.
Lemma lem48039 {A B : Type'} (a : A) (b : B) : (term13 A B a b) = ((term14 A B a b) = (@pair A B a b)).
Proof. exact (eq_refl (term13 A B a b)). Qed.
Lemma lem48040 {A B : Type'} (x : prod A B) : (term15 A B x) = (term15 A B x).
Proof. exact (eq_refl (term15 A B x)). Qed.
Lemma lem48041 {A B : Type'} (x : prod A B) (a : A) (b : B) : ((term12 A B x) = (term13 A B a b)) = ((term12 A B x) = ((term14 A B a b) = (@pair A B a b))).
Proof. exact (MK_COMB (@lem48040 A B x) (@lem48039 A B a b)). Qed.
Lemma lem48042 {A B : Type'} (x : prod A B) : (term12 A B x) = ((term16 A B x) = x).
Proof. exact (eq_refl (term12 A B x)). Qed.
Lemma lem48043 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem48044 {A B : Type'} (x : prod A B) : (term15 A B x) = (term17 A B x).
Proof. exact (MK_COMB (@lem48043) (@lem48042 A B x)). Qed.
Lemma lem48045 {A B : Type'} (a : A) (b : B) : ((term14 A B a b) = (@pair A B a b)) = ((term14 A B a b) = (@pair A B a b)).
Proof. exact (eq_refl ((term14 A B a b) = (@pair A B a b))). Qed.
Lemma lem48046 {A B : Type'} (x : prod A B) (a : A) (b : B) : ((term12 A B x) = ((term14 A B a b) = (@pair A B a b))) = (((term16 A B x) = x) = ((term14 A B a b) = (@pair A B a b))).
Proof. exact (MK_COMB (@lem48044 A B x) (@lem48045 A B a b)). Qed.
Lemma lem48047 {A B : Type'} (x : prod A B) (a : A) (b : B) : ((term12 A B x) = (term13 A B a b)) = (((term16 A B x) = x) = ((term14 A B a b) = (@pair A B a b))).
Proof. exact (TRANS (@lem48041 A B x a b) (@lem48046 A B x a b)). Qed.
Lemma lem48048 {A B : Type'} (x : prod A B) (a : A) (b : B) (h1 : x = (@pair A B a b)) : ((term16 A B x) = x) = ((term14 A B a b) = (@pair A B a b)).
Proof. exact (EQ_MP (@lem48047 A B x a b) (@lem48038 A B x a b h1)). Qed.
Lemma lem48049 {A B : Type'} (x : prod A B) (a : A) (b : B) (h1 : x = (@pair A B a b)) : ((term14 A B a b) = (@pair A B a b)) = ((term16 A B x) = x).
Proof. exact (SYM (@lem48048 A B x a b h1)). Qed.
Lemma lem48053 {A B : Type'} (y : B) (x : A) : (term7 A B x y) = x.
Proof. exact (EQ_MP (@lem48030 A B y x) (@lem48029 A B x y)). Qed.
Lemma lem48054 {A B : Type'} (y : B) (x : A) : (term7 A B x y) = x.
Proof. exact (@lem48053 A B y x). Qed.
Lemma lem48055 {A B : Type'} (b : B) (a : A) : (term7 A B a b) = a.
Proof. exact (@lem48054 A B b a). Qed.
Lemma lem48056 {A B : Type'} : (@pair A B) = (@pair A B).
Proof. exact (eq_refl (@pair A B)). Qed.
Lemma lem48057 {A B : Type'} (b : B) (a : A) : (term18 A B a b) = (@pair A B a).
Proof. exact (MK_COMB (@lem48056 A B) (@lem48055 A B b a)). Qed.
Lemma lem48059 {A B : Type'} (x : A) (y : B) : (term3 A B x y) = y.
Proof. exact (EQ_MP (@lem48024 A B x y) (@lem48023 A B x y)). Qed.
Lemma lem48060 {A B : Type'} (x : A) (y : B) : (term3 A B x y) = y.
Proof. exact (@lem48059 A B x y). Qed.
Lemma lem48061 {A B : Type'} (a : A) (b : B) : (term3 A B a b) = b.
Proof. exact (@lem48060 A B a b). Qed.
Lemma lem48062 {A B : Type'} (a : A) (b : B) : (term14 A B a b) = (@pair A B a b).
Proof. exact (MK_COMB (@lem48057 A B b a) (@lem48061 A B a b)). Qed.
Lemma lem48063 {A B : Type'} : (@eq (prod A B)) = (@eq (prod A B)).
Proof. exact (eq_refl (@eq (prod A B))). Qed.
Lemma lem48064 {A B : Type'} (a : A) (b : B) : (term19 A B a b) = (term20 A B a b).
Proof. exact (MK_COMB (@lem48063 A B) (@lem48062 A B a b)). Qed.
Lemma lem48065 {A B : Type'} (a : A) (b : B) : (@pair A B a b) = (@pair A B a b).
Proof. exact (eq_refl (@pair A B a b)). Qed.
Lemma lem48066 {A B : Type'} (a : A) (b : B) : ((term14 A B a b) = (@pair A B a b)) = ((@pair A B a b) = (@pair A B a b)).
Proof. exact (MK_COMB (@lem48064 A B a b) (@lem48065 A B a b)). Qed.
Lemma lem48068 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem48069 {A B : Type'} (x : prod A B) : (x = x) = True.
Proof. exact (@lem48068 (prod A B) x). Qed.
Lemma lem48070 {A B : Type'} (a : A) (b : B) : ((@pair A B a b) = (@pair A B a b)) = True.
Proof. exact (@lem48069 A B (@pair A B a b)). Qed.
Lemma lem48071 {A B : Type'} (a : A) (b : B) : ((term14 A B a b) = (@pair A B a b)) = True.
Proof. exact (TRANS (@lem48066 A B a b) (@lem48070 A B a b)). Qed.
Lemma lem48072 {A B : Type'} (a : A) (b : B) : True = ((term14 A B a b) = (@pair A B a b)).
Proof. exact (SYM (@lem48071 A B a b)). Qed.
Lemma lem48073 {A B : Type'} (a : A) (b : B) : (term14 A B a b) = (@pair A B a b).
Proof. exact (EQ_MP (@lem48072 A B a b) (@lem0)). Qed.
Lemma lem48074 {A B : Type'} (x : prod A B) (a : A) (b : B) (h1 : x = (@pair A B a b)) : (term16 A B x) = x.
Proof. exact (EQ_MP (@lem48049 A B x a b h1) (@lem48073 A B a b)). Qed.
Lemma lem48075 {A B : Type'} (x : prod A B) (a : A) (h1 : term10 A B x a) : (term16 A B x) = x.
Proof. exact (ex_elim (@lem48035 A B x a h1) (fun b : B => fun h0 : term21 A B x a b => @lem48074 A B x a b h0)). Qed.
Lemma lem48076 {A B : Type'} (x : prod A B) : (term16 A B x) = x.
Proof. exact (ex_elim (@lem48034 A B x) (fun a : A => fun h0 : term22 A B x a => @lem48075 A B x a h0)). Qed.
Lemma lem48081 {A B : Type'} : term23 A B.
Proof. exact (fun x : prod A B => @lem48076 A B x). Qed.
