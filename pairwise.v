Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import pairwise_term_abbrevs.
Lemma lem4794332 {_110510 : Type'} : (@pairwise _110510) = (term0 _110510).
Proof. exact (@pairwise_def _110510). Qed.
Lemma lem4794333 {_110510 : Type'} (_59319 : type1402 _110510) : _59319 = _59319.
Proof. exact (eq_refl _59319). Qed.
Lemma lem4794334 {_110510 : Type'} (_59319 : type1402 _110510) : (@pairwise _110510 _59319) = (term1 _110510 _59319).
Proof. exact (MK_COMB (@lem4794332 _110510) (@lem4794333 _110510 _59319)). Qed.
Lemma lem4794335 {_110510 : Type'} (_59319 : type1402 _110510) : (term1 _110510 _59319) = (term2 _110510 _59319).
Proof. exact (eq_refl (term1 _110510 _59319)). Qed.
Lemma lem4794336 {_110510 : Type'} (_59319 : type1402 _110510) : (@pairwise _110510 _59319) = (term2 _110510 _59319).
Proof. exact (TRANS (@lem4794334 _110510 _59319) (@lem4794335 _110510 _59319)). Qed.
Lemma lem4794337 {_110510 : Type'} (_59320 : _110510 -> Prop) : _59320 = _59320.
Proof. exact (eq_refl _59320). Qed.
Lemma lem4794338 {_110510 : Type'} (_59319 : type1402 _110510) (_59320 : _110510 -> Prop) : (@pairwise _110510 _59319 _59320) = (term3 _110510 _59319 _59320).
Proof. exact (MK_COMB (@lem4794336 _110510 _59319) (@lem4794337 _110510 _59320)). Qed.
Lemma lem4794339 {_110510 : Type'} (_59320 : _110510 -> Prop) (_59319 : type1402 _110510) : (term3 _110510 _59319 _59320) = (term4 _110510 _59320 _59319).
Proof. exact (eq_refl (term3 _110510 _59319 _59320)). Qed.
Lemma lem4794340 {_110510 : Type'} (_59320 : _110510 -> Prop) (_59319 : type1402 _110510) : (@pairwise _110510 _59319 _59320) = (term4 _110510 _59320 _59319).
Proof. exact (TRANS (@lem4794338 _110510 _59319 _59320) (@lem4794339 _110510 _59320 _59319)). Qed.
Lemma lem4794341 {_110510 : Type'} (_59319 : type1402 _110510) : term5 _110510 _59319.
Proof. exact (fun _59320 : _110510 -> Prop => @lem4794340 _110510 _59320 _59319). Qed.
Lemma lem4794342 {_110510 : Type'} : term6 _110510.
Proof. exact (fun _59319 : type1402 _110510 => @lem4794341 _110510 _59319). Qed.
Lemma lem4794343 {_110510 : Type'} (_59319 : type1402 _110510) : term7 _110510 _59319.
Proof. exact (@lem4794342 _110510 _59319). Qed.
Lemma lem4794344 {_110510 : Type'} (_59319 : type1402 _110510) : (term7 _110510 _59319) = (term5 _110510 _59319).
Proof. exact (eq_refl (term7 _110510 _59319)). Qed.
Lemma lem4794345 {_110510 : Type'} (_59319 : type1402 _110510) : term5 _110510 _59319.
Proof. exact (EQ_MP (@lem4794344 _110510 _59319) (@lem4794343 _110510 _59319)). Qed.
Lemma lem4794346 {_110510 : Type'} (_59319 : type1402 _110510) (_59320 : _110510 -> Prop) : term8 _110510 _59319 _59320.
Proof. exact (@lem4794345 _110510 _59319 _59320). Qed.
Lemma lem4794347 {_110510 : Type'} (_59320 : _110510 -> Prop) (_59319 : type1402 _110510) : (term8 _110510 _59319 _59320) = ((@pairwise _110510 _59319 _59320) = (term4 _110510 _59320 _59319)).
Proof. exact (eq_refl (term8 _110510 _59319 _59320)). Qed.
Lemma lem4794348 {_110510 : Type'} (_59320 : _110510 -> Prop) (_59319 : type1402 _110510) : (@pairwise _110510 _59319 _59320) = (term4 _110510 _59320 _59319).
Proof. exact (EQ_MP (@lem4794347 _110510 _59320 _59319) (@lem4794346 _110510 _59319 _59320)). Qed.
Lemma lem4794391 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (@pairwise _110510 r s) = (term4 _110510 s r).
Proof. exact (@lem4794348 _110510 s r). Qed.
Lemma lem4794392 {_110510 : Type'} (s : _110510 -> Prop) : term9 _110510 s.
Proof. exact (fun r : type1402 _110510 => @lem4794391 _110510 s r). Qed.
Lemma lem4794393 {_110510 : Type'} : term10 _110510.
Proof. exact (fun s : _110510 -> Prop => @lem4794392 _110510 s). Qed.
