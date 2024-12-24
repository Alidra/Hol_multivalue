Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3183254_term_abbrevs.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3183080_spec.
Require Import thm3183081_spec.
Lemma lem3183236 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3183081 A P x) (@lem3183080 A P x)). Qed.
Lemma lem3183237 {_83169 : Type'} (P : _83169 -> Prop) (x : _83169) : (@IN _83169 x P) = (P x).
Proof. exact (@lem3183236 _83169 P x). Qed.
Lemma lem3183238 {_83169 : Type'} (p : _83169 -> Prop) (x : _83169) : (term0 _83169 x p) = (term1 _83169 p x).
Proof. exact (@lem3183237 _83169 (term2 _83169 p) x). Qed.
Lemma lem3183240 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3183241 {_83169 : Type'} (f : _83169 -> Prop) (y : _83169) : (term1 _83169 f y) = (f y).
Proof. exact (@lem3183240 _83169 Prop f y). Qed.
Lemma lem3183242 {_83169 : Type'} (p : _83169 -> Prop) (x : _83169) : (term1 _83169 p x) = (p x).
Proof. exact (@lem3183241 _83169 p x). Qed.
Lemma lem3183243 {_83169 : Type'} (p : _83169 -> Prop) (x : _83169) : (term0 _83169 x p) = (p x).
Proof. exact (TRANS (@lem3183238 _83169 p x) (@lem3183242 _83169 p x)). Qed.
Lemma lem3183244 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3183245 {_83169 : Type'} (p : _83169 -> Prop) (x : _83169) : (term4 _83169 x p) = (term5 _83169 p x).
Proof. exact (MK_COMB (@lem3183244) (@lem3183243 _83169 p x)). Qed.
Lemma lem3183246 {_83169 : Type'} (p : _83169 -> Prop) (x : _83169) : (p x) = (p x).
Proof. exact (eq_refl (p x)). Qed.
Lemma lem3183247 {_83169 : Type'} (p : _83169 -> Prop) (x : _83169) : ((term0 _83169 x p) = (p x)) = ((p x) = (p x)).
Proof. exact (MK_COMB (@lem3183245 _83169 p x) (@lem3183246 _83169 p x)). Qed.
Lemma lem3183249 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3183250 (x : Prop) : (x = x) = True.
Proof. exact (@lem3183249 Prop x). Qed.
Lemma lem3183251 {_83169 : Type'} (p : _83169 -> Prop) (x : _83169) : ((p x) = (p x)) = True.
Proof. exact (@lem3183250 (p x)). Qed.
Lemma lem3183252 {_83169 : Type'} (p : _83169 -> Prop) (x : _83169) : ((term0 _83169 x p) = (p x)) = True.
Proof. exact (TRANS (@lem3183247 _83169 p x) (@lem3183251 _83169 p x)). Qed.
Lemma lem3183253 {_83169 : Type'} (p : _83169 -> Prop) (x : _83169) : True = ((term0 _83169 x p) = (p x)).
Proof. exact (SYM (@lem3183252 _83169 p x)). Qed.
Lemma lem3183254 {_83169 : Type'} (p : _83169 -> Prop) (x : _83169) : (term0 _83169 x p) = (p x).
Proof. exact (EQ_MP (@lem3183253 _83169 p x) (@lem0)). Qed.
