Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7932389_term_abbrevs.
Require Import SURJECTIVE_IMAGE_EQ_spec.
Lemma lem7932369 {_88266 _88270 : Type'} (f : _88270 -> _88266) (h1 : term0 _88266 _88270 f) : term0 _88266 _88270 f.
Proof. exact (h1). Qed.
Lemma lem7932370 {_88266 _88270 : Type'} (s : _88270 -> Prop) (f : _88270 -> _88266) (h1 : term0 _88266 _88270 f) : term1 _88266 _88270 f s.
Proof. exact (@lem7932369 _88266 _88270 f h1 s). Qed.
Lemma lem7932371 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) : (term1 _88266 _88270 f s) = (term2 _88266 _88270 f s).
Proof. exact (eq_refl (term1 _88266 _88270 f s)). Qed.
Lemma lem7932372 {_88266 _88270 : Type'} (s : _88270 -> Prop) (f : _88270 -> _88266) (h1 : term0 _88266 _88270 f) : term2 _88266 _88270 f s.
Proof. exact (EQ_MP (@lem7932371 _88266 _88270 f s) (@lem7932370 _88266 _88270 s f h1)). Qed.
Lemma lem7932373 {_88266 _88270 : Type'} (s : _88270 -> Prop) (t : _88266 -> Prop) (f : _88270 -> _88266) (h1 : term0 _88266 _88270 f) : term3 _88266 _88270 f s t.
Proof. exact (@lem7932372 _88266 _88270 s f h1 t). Qed.
Lemma lem7932374 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) : (term3 _88266 _88270 f s t) = (term4 _88266 _88270 f s t).
Proof. exact (eq_refl (term3 _88266 _88270 f s t)). Qed.
Lemma lem7932375 {_88266 _88270 : Type'} (s : _88270 -> Prop) (t : _88266 -> Prop) (f : _88270 -> _88266) (h1 : term0 _88266 _88270 f) : term4 _88266 _88270 f s t.
Proof. exact (EQ_MP (@lem7932374 _88266 _88270 f s t) (@lem7932373 _88266 _88270 s t f h1)). Qed.
Lemma lem7932376 {_88266 _88270 : Type'} (f : _88270 -> _88266) (t : _88266 -> Prop) (s : _88270 -> Prop) (h1 : term5 _88266 _88270 f t s) : term5 _88266 _88270 f t s.
Proof. exact (h1). Qed.
Lemma lem7932377 {_88266 _88270 : Type'} (f : _88270 -> _88266) (t : _88266 -> Prop) (s : _88270 -> Prop) (h1 : term0 _88266 _88270 f) (h2 : term5 _88266 _88270 f t s) : (@IMAGE _88270 _88266 f s) = t.
Proof. exact (@lem7932375 _88266 _88270 s t f h1 (@lem7932376 _88266 _88270 f t s h2)). Qed.
Lemma lem7932378 {_88266 _88270 : Type'} (f : _88270 -> _88266) (t : _88266 -> Prop) (s : _88270 -> Prop) (h1 : term5 _88266 _88270 f t s) : term6 _88266 _88270 f s t.
Proof. exact (fun h0 : term0 _88266 _88270 f => @lem7932377 _88266 _88270 f t s h0 h1). Qed.
Lemma lem7932379 {_88266 _88270 : Type'} (f : _88270 -> _88266) (h1 : term0 _88266 _88270 f) : term0 _88266 _88270 f.
Proof. exact (h1). Qed.
Lemma lem7932380 {_88266 _88270 : Type'} (f : _88270 -> _88266) (t : _88266 -> Prop) (s : _88270 -> Prop) (h1 : term0 _88266 _88270 f) (h2 : term5 _88266 _88270 f t s) : (@IMAGE _88270 _88266 f s) = t.
Proof. exact (@lem7932378 _88266 _88270 f t s h2 (@lem7932379 _88266 _88270 f h1)). Qed.
Lemma lem7932381 {_88266 _88270 : Type'} (s : _88270 -> Prop) (t : _88266 -> Prop) (f : _88270 -> _88266) (h1 : term0 _88266 _88270 f) : term4 _88266 _88270 f s t.
Proof. exact (fun h0 : term5 _88266 _88270 f t s => @lem7932380 _88266 _88270 f t s h1 h0). Qed.
Lemma lem7932382 {_88266 _88270 : Type'} (s : _88270 -> Prop) (f : _88270 -> _88266) (h1 : term0 _88266 _88270 f) : term2 _88266 _88270 f s.
Proof. exact (fun t : _88266 -> Prop => @lem7932381 _88266 _88270 s t f h1). Qed.
Lemma lem7932383 {_88266 _88270 : Type'} (f : _88270 -> _88266) (h1 : term0 _88266 _88270 f) : term0 _88266 _88270 f.
Proof. exact (fun s : _88270 -> Prop => @lem7932382 _88266 _88270 s f h1). Qed.
Lemma lem7932384 {_88266 _88270 : Type'} (f : _88270 -> _88266) : term7 _88266 _88270 f.
Proof. exact (fun h0 : term0 _88266 _88270 f => @lem7932383 _88266 _88270 f h0). Qed.
Lemma lem7932385 {_88266 _88270 : Type'} (f : _88270 -> _88266) : term0 _88266 _88270 f.
Proof. exact (@lem7932384 _88266 _88270 f (@lem3399677 _88266 _88270 f)). Qed.
Lemma lem7932386 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) : term1 _88266 _88270 f s.
Proof. exact (@lem7932385 _88266 _88270 f s). Qed.
Lemma lem7932387 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) : (term1 _88266 _88270 f s) = (term2 _88266 _88270 f s).
Proof. exact (eq_refl (term1 _88266 _88270 f s)). Qed.
Lemma lem7932388 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) : term2 _88266 _88270 f s.
Proof. exact (EQ_MP (@lem7932387 _88266 _88270 f s) (@lem7932386 _88266 _88270 f s)). Qed.
Lemma lem7932389 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) : term3 _88266 _88270 f s t.
Proof. exact (@lem7932388 _88266 _88270 f s t). Qed.
