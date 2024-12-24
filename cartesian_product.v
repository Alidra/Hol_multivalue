Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import cartesian_product_term_abbrevs.
Lemma lem4399383 {A K : Type'} : (@cartesian_product A K) = (term0 A K).
Proof. exact (@cartesian_product_def A K). Qed.
Lemma lem4399384 {K : Type'} (_50293 : K -> Prop) : _50293 = _50293.
Proof. exact (eq_refl _50293). Qed.
Lemma lem4399385 {A K : Type'} (_50293 : K -> Prop) : (@cartesian_product A K _50293) = (term1 A K _50293).
Proof. exact (MK_COMB (@lem4399383 A K) (@lem4399384 K _50293)). Qed.
Lemma lem4399386 {A K : Type'} (_50293 : K -> Prop) : (term1 A K _50293) = (term2 A K _50293).
Proof. exact (eq_refl (term1 A K _50293)). Qed.
Lemma lem4399387 {A K : Type'} (_50293 : K -> Prop) : (@cartesian_product A K _50293) = (term2 A K _50293).
Proof. exact (TRANS (@lem4399385 A K _50293) (@lem4399386 A K _50293)). Qed.
Lemma lem4399388 {A K : Type'} (_50294 : type1470 A K) : _50294 = _50294.
Proof. exact (eq_refl _50294). Qed.
Lemma lem4399389 {A K : Type'} (_50293 : K -> Prop) (_50294 : type1470 A K) : (@cartesian_product A K _50293 _50294) = (term3 A K _50293 _50294).
Proof. exact (MK_COMB (@lem4399387 A K _50293) (@lem4399388 A K _50294)). Qed.
Lemma lem4399390 {A K : Type'} (_50293 : K -> Prop) (_50294 : type1470 A K) : (term3 A K _50293 _50294) = (term4 A K _50293 _50294).
Proof. exact (eq_refl (term3 A K _50293 _50294)). Qed.
Lemma lem4399391 {A K : Type'} (_50293 : K -> Prop) (_50294 : type1470 A K) : (@cartesian_product A K _50293 _50294) = (term4 A K _50293 _50294).
Proof. exact (TRANS (@lem4399389 A K _50293 _50294) (@lem4399390 A K _50293 _50294)). Qed.
Lemma lem4399392 {A K : Type'} (_50293 : K -> Prop) : term5 A K _50293.
Proof. exact (fun _50294 : type1470 A K => @lem4399391 A K _50293 _50294). Qed.
Lemma lem4399393 {A K : Type'} : term6 A K.
Proof. exact (fun _50293 : K -> Prop => @lem4399392 A K _50293). Qed.
Lemma lem4399394 {A K : Type'} (_50293 : K -> Prop) : term7 A K _50293.
Proof. exact (@lem4399393 A K _50293). Qed.
Lemma lem4399395 {A K : Type'} (_50293 : K -> Prop) : (term7 A K _50293) = (term5 A K _50293).
Proof. exact (eq_refl (term7 A K _50293)). Qed.
Lemma lem4399396 {A K : Type'} (_50293 : K -> Prop) : term5 A K _50293.
Proof. exact (EQ_MP (@lem4399395 A K _50293) (@lem4399394 A K _50293)). Qed.
Lemma lem4399397 {A K : Type'} (_50293 : K -> Prop) (_50294 : type1470 A K) : term8 A K _50293 _50294.
Proof. exact (@lem4399396 A K _50293 _50294). Qed.
Lemma lem4399398 {A K : Type'} (_50293 : K -> Prop) (_50294 : type1470 A K) : (term8 A K _50293 _50294) = ((@cartesian_product A K _50293 _50294) = (term4 A K _50293 _50294)).
Proof. exact (eq_refl (term8 A K _50293 _50294)). Qed.
Lemma lem4399399 {A K : Type'} (_50293 : K -> Prop) (_50294 : type1470 A K) : (@cartesian_product A K _50293 _50294) = (term4 A K _50293 _50294).
Proof. exact (EQ_MP (@lem4399398 A K _50293 _50294) (@lem4399397 A K _50293 _50294)). Qed.
Lemma lem4399442 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term4 A K k s).
Proof. exact (@lem4399399 A K k s). Qed.
Lemma lem4399443 {A K : Type'} (k : K -> Prop) : term5 A K k.
Proof. exact (fun s : type1470 A K => @lem4399442 A K k s). Qed.
Lemma lem4399444 {A K : Type'} : term6 A K.
Proof. exact (fun k : K -> Prop => @lem4399443 A K k). Qed.
