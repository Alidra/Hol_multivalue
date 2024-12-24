Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7931587_term_abbrevs.
Require Import SURJECTIVE_IMAGE_EQ_spec.
Lemma lem7931567 {_88266 _88270 : Type'} (f : _88270 -> _88266) (h1 : term0 _88266 _88270 f) : term0 _88266 _88270 f.
Proof. exact (h1). Qed.
Lemma lem7931568 {_88266 _88270 : Type'} (s : _88270 -> Prop) (f : _88270 -> _88266) (h1 : term0 _88266 _88270 f) : term1 _88266 _88270 f s.
Proof. exact (@lem7931567 _88266 _88270 f h1 s). Qed.
Lemma lem7931569 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) : (term1 _88266 _88270 f s) = (term2 _88266 _88270 f s).
Proof. exact (eq_refl (term1 _88266 _88270 f s)). Qed.
Lemma lem7931570 {_88266 _88270 : Type'} (s : _88270 -> Prop) (f : _88270 -> _88266) (h1 : term0 _88266 _88270 f) : term2 _88266 _88270 f s.
Proof. exact (EQ_MP (@lem7931569 _88266 _88270 f s) (@lem7931568 _88266 _88270 s f h1)). Qed.
Lemma lem7931571 {_88266 _88270 : Type'} (s : _88270 -> Prop) (t : _88266 -> Prop) (f : _88270 -> _88266) (h1 : term0 _88266 _88270 f) : term3 _88266 _88270 f s t.
Proof. exact (@lem7931570 _88266 _88270 s f h1 t). Qed.
Lemma lem7931572 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) : (term3 _88266 _88270 f s t) = (term4 _88266 _88270 f s t).
Proof. exact (eq_refl (term3 _88266 _88270 f s t)). Qed.
Lemma lem7931573 {_88266 _88270 : Type'} (s : _88270 -> Prop) (t : _88266 -> Prop) (f : _88270 -> _88266) (h1 : term0 _88266 _88270 f) : term4 _88266 _88270 f s t.
Proof. exact (EQ_MP (@lem7931572 _88266 _88270 f s t) (@lem7931571 _88266 _88270 s t f h1)). Qed.
Lemma lem7931574 {_88266 _88270 : Type'} (f : _88270 -> _88266) (t : _88266 -> Prop) (s : _88270 -> Prop) (h1 : term5 _88266 _88270 f t s) : term5 _88266 _88270 f t s.
Proof. exact (h1). Qed.
Lemma lem7931575 {_88266 _88270 : Type'} (f : _88270 -> _88266) (t : _88266 -> Prop) (s : _88270 -> Prop) (h1 : term0 _88266 _88270 f) (h2 : term5 _88266 _88270 f t s) : (@IMAGE _88270 _88266 f s) = t.
Proof. exact (@lem7931573 _88266 _88270 s t f h1 (@lem7931574 _88266 _88270 f t s h2)). Qed.
Lemma lem7931576 {_88266 _88270 : Type'} (f : _88270 -> _88266) (t : _88266 -> Prop) (s : _88270 -> Prop) (h1 : term5 _88266 _88270 f t s) : term6 _88266 _88270 f s t.
Proof. exact (fun h0 : term0 _88266 _88270 f => @lem7931575 _88266 _88270 f t s h0 h1). Qed.
Lemma lem7931577 {_88266 _88270 : Type'} (f : _88270 -> _88266) (h1 : term0 _88266 _88270 f) : term0 _88266 _88270 f.
Proof. exact (h1). Qed.
Lemma lem7931578 {_88266 _88270 : Type'} (f : _88270 -> _88266) (t : _88266 -> Prop) (s : _88270 -> Prop) (h1 : term0 _88266 _88270 f) (h2 : term5 _88266 _88270 f t s) : (@IMAGE _88270 _88266 f s) = t.
Proof. exact (@lem7931576 _88266 _88270 f t s h2 (@lem7931577 _88266 _88270 f h1)). Qed.
Lemma lem7931579 {_88266 _88270 : Type'} (s : _88270 -> Prop) (t : _88266 -> Prop) (f : _88270 -> _88266) (h1 : term0 _88266 _88270 f) : term4 _88266 _88270 f s t.
Proof. exact (fun h0 : term5 _88266 _88270 f t s => @lem7931578 _88266 _88270 f t s h1 h0). Qed.
Lemma lem7931580 {_88266 _88270 : Type'} (s : _88270 -> Prop) (f : _88270 -> _88266) (h1 : term0 _88266 _88270 f) : term2 _88266 _88270 f s.
Proof. exact (fun t : _88266 -> Prop => @lem7931579 _88266 _88270 s t f h1). Qed.
Lemma lem7931581 {_88266 _88270 : Type'} (f : _88270 -> _88266) (h1 : term0 _88266 _88270 f) : term0 _88266 _88270 f.
Proof. exact (fun s : _88270 -> Prop => @lem7931580 _88266 _88270 s f h1). Qed.
Lemma lem7931582 {_88266 _88270 : Type'} (f : _88270 -> _88266) : term7 _88266 _88270 f.
Proof. exact (fun h0 : term0 _88266 _88270 f => @lem7931581 _88266 _88270 f h0). Qed.
Lemma lem7931583 {_88266 _88270 : Type'} (f : _88270 -> _88266) : term0 _88266 _88270 f.
Proof. exact (@lem7931582 _88266 _88270 f (@lem3399677 _88266 _88270 f)). Qed.
Lemma lem7931584 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) : term1 _88266 _88270 f s.
Proof. exact (@lem7931583 _88266 _88270 f s). Qed.
Lemma lem7931585 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) : (term1 _88266 _88270 f s) = (term2 _88266 _88270 f s).
Proof. exact (eq_refl (term1 _88266 _88270 f s)). Qed.
Lemma lem7931586 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) : term2 _88266 _88270 f s.
Proof. exact (EQ_MP (@lem7931585 _88266 _88270 f s) (@lem7931584 _88266 _88270 f s)). Qed.
Lemma lem7931587 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) : term3 _88266 _88270 f s t.
Proof. exact (@lem7931586 _88266 _88270 f s t). Qed.
