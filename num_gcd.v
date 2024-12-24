Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import num_gcd_term_abbrevs.
Require Import FST_spec.
Require Import SND_spec.
Lemma lem2839253 : num_gcd = term0.
Proof. exact (@num_gcd_def). Qed.
Lemma lem2839254 (_31181 : prod nat nat) : _31181 = _31181.
Proof. exact (eq_refl _31181). Qed.
Lemma lem2839255 (_31181 : prod nat nat) : (num_gcd _31181) = (term1 _31181).
Proof. exact (MK_COMB (@lem2839253) (@lem2839254 _31181)). Qed.
Lemma lem2839256 (_31181 : prod nat nat) : (term1 _31181) = (term2 _31181).
Proof. exact (eq_refl (term1 _31181)). Qed.
Lemma lem2839257 (_31181 : prod nat nat) : (num_gcd _31181) = (term2 _31181).
Proof. exact (TRANS (@lem2839255 _31181) (@lem2839256 _31181)). Qed.
Lemma lem2839258 : term3.
Proof. exact (fun _31181 : prod nat nat => @lem2839257 _31181). Qed.
Lemma lem2839259 (_31181 : prod nat nat) : term4 _31181.
Proof. exact (@lem2839258 _31181). Qed.
Lemma lem2839260 (_31181 : prod nat nat) : (term4 _31181) = ((num_gcd _31181) = (term2 _31181)).
Proof. exact (eq_refl (term4 _31181)). Qed.
Lemma lem2839261 (_31181 : prod nat nat) : (num_gcd _31181) = (term2 _31181).
Proof. exact (EQ_MP (@lem2839260 _31181) (@lem2839259 _31181)). Qed.
Lemma lem2839262 (a : nat) (b : nat) : (term5 a b) = (term6 a b).
Proof. exact (@lem2839261 (@pair nat nat a b)). Qed.
Lemma lem2839263 {A B : Type'} (x : A) : term7 A B x.
Proof. exact (@lem48019 A B x). Qed.
Lemma lem2839264 {A B : Type'} (x : A) : (term7 A B x) = (term8 A B x).
Proof. exact (eq_refl (term7 A B x)). Qed.
Lemma lem2839265 {A B : Type'} (x : A) : term8 A B x.
Proof. exact (EQ_MP (@lem2839264 A B x) (@lem2839263 A B x)). Qed.
Lemma lem2839266 {A B : Type'} (x : A) (y : B) : term9 A B x y.
Proof. exact (@lem2839265 A B x y). Qed.
Lemma lem2839267 {A B : Type'} (x : A) (y : B) : (term9 A B x y) = ((term10 A B x y) = y).
Proof. exact (eq_refl (term9 A B x y)). Qed.
Lemma lem2839269 {A B : Type'} (x : A) : term11 A B x.
Proof. exact (@lem47827 A B x). Qed.
Lemma lem2839270 {A B : Type'} (x : A) : (term11 A B x) = (term12 A B x).
Proof. exact (eq_refl (term11 A B x)). Qed.
Lemma lem2839271 {A B : Type'} (x : A) : term12 A B x.
Proof. exact (EQ_MP (@lem2839270 A B x) (@lem2839269 A B x)). Qed.
Lemma lem2839272 {A B : Type'} (x : A) (y : B) : term13 A B x y.
Proof. exact (@lem2839271 A B x y). Qed.
Lemma lem2839273 {A B : Type'} (y : B) (x : A) : (term13 A B x y) = ((term14 A B x y) = x).
Proof. exact (eq_refl (term13 A B x y)). Qed.
Lemma lem2839276 {A B : Type'} (y : B) (x : A) : (term14 A B x y) = x.
Proof. exact (EQ_MP (@lem2839273 A B y x) (@lem2839272 A B x y)). Qed.
Lemma lem2839277 (y : nat) (x : nat) : (term15 x y) = x.
Proof. exact (@lem2839276 nat nat y x). Qed.
Lemma lem2839278 (b : nat) (a : nat) : (term15 a b) = a.
Proof. exact (@lem2839277 b a). Qed.
Lemma lem2839279 (a : nat) (b : nat) : a = (term15 a b).
Proof. exact (SYM (@lem2839278 b a)). Qed.
Lemma lem2839281 {A B : Type'} (x : A) (y : B) : (term10 A B x y) = y.
Proof. exact (EQ_MP (@lem2839267 A B x y) (@lem2839266 A B x y)). Qed.
Lemma lem2839282 (x : nat) (y : nat) : (term16 x y) = y.
Proof. exact (@lem2839281 nat nat x y). Qed.
Lemma lem2839283 (a : nat) (b : nat) : (term16 a b) = b.
Proof. exact (@lem2839282 a b). Qed.
Lemma lem2839284 (a : nat) (b : nat) : b = (term16 a b).
Proof. exact (SYM (@lem2839283 a b)). Qed.
Lemma lem2839285 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem2839286 (a : nat) (b : nat) : (term18 a) = (term19 a b).
Proof. exact (MK_COMB (@lem2839285) (@lem2839279 a b)). Qed.
Lemma lem2839287 (a : nat) (b : nat) : (term19 a b) = (term20 a b).
Proof. exact (eq_refl (term19 a b)). Qed.
Lemma lem2839288 (a : nat) : (term21 a) = (term21 a).
Proof. exact (eq_refl (term21 a)). Qed.
Lemma lem2839289 (a : nat) (b : nat) : ((term18 a) = (term19 a b)) = ((term18 a) = (term20 a b)).
Proof. exact (MK_COMB (@lem2839288 a) (@lem2839287 a b)). Qed.
Lemma lem2839290 (a : nat) : (term18 a) = (term22 a).
Proof. exact (eq_refl (term18 a)). Qed.
Lemma lem2839291 : (@eq (nat -> nat)) = (@eq (nat -> nat)).
Proof. exact (eq_refl (@eq (nat -> nat))). Qed.
Lemma lem2839292 (a : nat) : (term21 a) = (term23 a).
Proof. exact (MK_COMB (@lem2839291) (@lem2839290 a)). Qed.
Lemma lem2839293 (a : nat) (b : nat) : (term20 a b) = (term20 a b).
Proof. exact (eq_refl (term20 a b)). Qed.
Lemma lem2839294 (a : nat) (b : nat) : ((term18 a) = (term20 a b)) = ((term22 a) = (term20 a b)).
Proof. exact (MK_COMB (@lem2839292 a) (@lem2839293 a b)). Qed.
Lemma lem2839295 (a : nat) (b : nat) : ((term18 a) = (term19 a b)) = ((term22 a) = (term20 a b)).
Proof. exact (TRANS (@lem2839289 a b) (@lem2839294 a b)). Qed.
Lemma lem2839296 (a : nat) (b : nat) : (term22 a) = (term20 a b).
Proof. exact (EQ_MP (@lem2839295 a b) (@lem2839286 a b)). Qed.
Lemma lem2839297 (a : nat) (b : nat) : (term24 a b) = (term25 a b).
Proof. exact (MK_COMB (@lem2839296 a b) (@lem2839284 a b)). Qed.
Lemma lem2839298 (a : nat) (b : nat) : (term25 a b) = (term6 a b).
Proof. exact (eq_refl (term25 a b)). Qed.
Lemma lem2839299 (a : nat) (b : nat) : (term26 a b) = (term26 a b).
Proof. exact (eq_refl (term26 a b)). Qed.
Lemma lem2839300 (a : nat) (b : nat) : ((term24 a b) = (term25 a b)) = ((term24 a b) = (term6 a b)).
Proof. exact (MK_COMB (@lem2839299 a b) (@lem2839298 a b)). Qed.
Lemma lem2839301 (a : nat) (b : nat) : (term24 a b) = (term27 a b).
Proof. exact (eq_refl (term24 a b)). Qed.
Lemma lem2839302 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem2839303 (a : nat) (b : nat) : (term26 a b) = (term28 a b).
Proof. exact (MK_COMB (@lem2839302) (@lem2839301 a b)). Qed.
Lemma lem2839304 (a : nat) (b : nat) : (term6 a b) = (term6 a b).
Proof. exact (eq_refl (term6 a b)). Qed.
Lemma lem2839305 (a : nat) (b : nat) : ((term24 a b) = (term6 a b)) = ((term27 a b) = (term6 a b)).
Proof. exact (MK_COMB (@lem2839303 a b) (@lem2839304 a b)). Qed.
Lemma lem2839306 (a : nat) (b : nat) : ((term24 a b) = (term25 a b)) = ((term27 a b) = (term6 a b)).
Proof. exact (TRANS (@lem2839300 a b) (@lem2839305 a b)). Qed.
Lemma lem2839307 (a : nat) (b : nat) : (term27 a b) = (term6 a b).
Proof. exact (EQ_MP (@lem2839306 a b) (@lem2839297 a b)). Qed.
Lemma lem2839308 (a : nat) (b : nat) : (term6 a b) = (term27 a b).
Proof. exact (SYM (@lem2839307 a b)). Qed.
Lemma lem2839309 (a : nat) (b : nat) : (term5 a b) = (term27 a b).
Proof. exact (TRANS (@lem2839262 a b) (@lem2839308 a b)). Qed.
Lemma lem2839310 (a : nat) : term29 a.
Proof. exact (fun b : nat => @lem2839309 a b). Qed.
Lemma lem2839311 : term30.
Proof. exact (fun a : nat => @lem2839310 a). Qed.
