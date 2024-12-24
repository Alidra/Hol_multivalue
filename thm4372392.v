Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4372392_term_abbrevs.
Require Import thm13473_spec.
Lemma lem4372375 {_105011 _105012 : Type'} (_474 : type1210 _105011 _105012) (_475 : Prop) (_476 : type324 _105011 _105012) (_477 : type1210 _105011 _105012) : (term0 _105011 _105012 _476 _475 _474 _477) = (term1 _105011 _105012 _474 _475 _476 _477).
Proof. exact (@lem13473 (type1210 _105011 _105012) _474 _475 _476 _477). Qed.
Lemma lem4372376 {_105011 _105012 : Type'} (_474 : type1210 _105011 _105012) (_475 : Prop) (f : type686 _105011) (t : _105012 -> Prop) (_477 : type1210 _105011 _105012) : (term2 _105011 _105012 f t _475 _474 _477) = (term3 _105011 _105012 _474 _475 f t _477).
Proof. exact (@lem4372375 _105011 _105012 _474 _475 (term4 _105011 _105012 f t) _477). Qed.
Lemma lem4372377 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term5 _105011 _105012 f t) = (term6 _105011 _105012 f t).
Proof. exact (@lem4372376 _105011 _105012 (@CROSS _105012 _105011 (@UNIV _105011) t) (f = (@EMPTY (_105011 -> Prop))) f t (term7 _105011 _105012 f t)). Qed.
Lemma lem4372378 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term8 _105011 _105012 f t) = ((term9 _105011 _105012 f t) = (term7 _105011 _105012 f t)).
Proof. exact (eq_refl (term8 _105011 _105012 f t)). Qed.
Lemma lem4372379 {_105011 : Type'} (f : type686 _105011) : (term10 _105011 f) = (term10 _105011 f).
Proof. exact (eq_refl (term10 _105011 f)). Qed.
Lemma lem4372380 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term11 _105011 _105012 f t) = (term12 _105011 _105012 f t).
Proof. exact (MK_COMB (@lem4372379 _105011 f) (@lem4372378 _105011 _105012 f t)). Qed.
Lemma lem4372381 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term13 _105011 _105012 f t) = ((term9 _105011 _105012 f t) = (@CROSS _105012 _105011 (@UNIV _105011) t)).
Proof. exact (eq_refl (term13 _105011 _105012 f t)). Qed.
Lemma lem4372382 {_105011 : Type'} (f : type686 _105011) : (term14 _105011 f) = (term14 _105011 f).
Proof. exact (eq_refl (term14 _105011 f)). Qed.
Lemma lem4372383 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term15 _105011 _105012 f t) = (term16 _105011 _105012 f t).
Proof. exact (MK_COMB (@lem4372382 _105011 f) (@lem4372381 _105011 _105012 f t)). Qed.
Lemma lem4372384 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4372385 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term17 _105011 _105012 f t) = (term18 _105011 _105012 f t).
Proof. exact (MK_COMB (@lem4372384) (@lem4372383 _105011 _105012 f t)). Qed.
Lemma lem4372386 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term6 _105011 _105012 f t) = (term19 _105011 _105012 f t).
Proof. exact (MK_COMB (@lem4372385 _105011 _105012 f t) (@lem4372380 _105011 _105012 f t)). Qed.
Lemma lem4372387 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term5 _105011 _105012 f t) = ((term9 _105011 _105012 f t) = (term20 _105011 _105012 f t)).
Proof. exact (eq_refl (term5 _105011 _105012 f t)). Qed.
Lemma lem4372388 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4372389 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term21 _105011 _105012 f t) = (term22 _105011 _105012 f t).
Proof. exact (MK_COMB (@lem4372388) (@lem4372387 _105011 _105012 f t)). Qed.
Lemma lem4372390 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : ((term5 _105011 _105012 f t) = (term6 _105011 _105012 f t)) = (((term9 _105011 _105012 f t) = (term20 _105011 _105012 f t)) = (term19 _105011 _105012 f t)).
Proof. exact (MK_COMB (@lem4372389 _105011 _105012 f t) (@lem4372386 _105011 _105012 f t)). Qed.
Lemma lem4372391 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : ((term9 _105011 _105012 f t) = (term20 _105011 _105012 f t)) = (term19 _105011 _105012 f t).
Proof. exact (EQ_MP (@lem4372390 _105011 _105012 f t) (@lem4372377 _105011 _105012 f t)). Qed.
Lemma lem4372392 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term19 _105011 _105012 f t) = ((term9 _105011 _105012 f t) = (term20 _105011 _105012 f t)).
Proof. exact (SYM (@lem4372391 _105011 _105012 f t)). Qed.
