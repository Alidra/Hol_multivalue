Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4372328_term_abbrevs.
Require Import thm13473_spec.
Lemma lem4372311 {_104960 _104961 : Type'} (_474 : type1210 _104960 _104961) (_475 : Prop) (_476 : type324 _104960 _104961) (_477 : type1210 _104960 _104961) : (term0 _104960 _104961 _476 _475 _474 _477) = (term1 _104960 _104961 _474 _475 _476 _477).
Proof. exact (@lem13473 (type1210 _104960 _104961) _474 _475 _476 _477). Qed.
Lemma lem4372312 {_104960 _104961 : Type'} (_474 : type1210 _104960 _104961) (_475 : Prop) (s : _104960 -> Prop) (f : type686 _104961) (_477 : type1210 _104960 _104961) : (term2 _104960 _104961 s f _475 _474 _477) = (term3 _104960 _104961 _474 _475 s f _477).
Proof. exact (@lem4372311 _104960 _104961 _474 _475 (term4 _104960 _104961 s f) _477). Qed.
Lemma lem4372313 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term5 _104960 _104961 f s) = (term6 _104960 _104961 f s).
Proof. exact (@lem4372312 _104960 _104961 (@CROSS _104961 _104960 s (@UNIV _104961)) (f = (@EMPTY (_104961 -> Prop))) s f (term7 _104960 _104961 f s)). Qed.
Lemma lem4372314 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term8 _104960 _104961 f s) = ((term9 _104960 _104961 s f) = (term7 _104960 _104961 f s)).
Proof. exact (eq_refl (term8 _104960 _104961 f s)). Qed.
Lemma lem4372315 {_104961 : Type'} (f : type686 _104961) : (term10 _104961 f) = (term10 _104961 f).
Proof. exact (eq_refl (term10 _104961 f)). Qed.
Lemma lem4372316 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term11 _104960 _104961 f s) = (term12 _104960 _104961 f s).
Proof. exact (MK_COMB (@lem4372315 _104961 f) (@lem4372314 _104960 _104961 f s)). Qed.
Lemma lem4372317 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term13 _104960 _104961 f s) = ((term9 _104960 _104961 s f) = (@CROSS _104961 _104960 s (@UNIV _104961))).
Proof. exact (eq_refl (term13 _104960 _104961 f s)). Qed.
Lemma lem4372318 {_104961 : Type'} (f : type686 _104961) : (term14 _104961 f) = (term14 _104961 f).
Proof. exact (eq_refl (term14 _104961 f)). Qed.
Lemma lem4372319 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term15 _104960 _104961 f s) = (term16 _104960 _104961 f s).
Proof. exact (MK_COMB (@lem4372318 _104961 f) (@lem4372317 _104960 _104961 f s)). Qed.
Lemma lem4372320 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4372321 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term17 _104960 _104961 f s) = (term18 _104960 _104961 f s).
Proof. exact (MK_COMB (@lem4372320) (@lem4372319 _104960 _104961 f s)). Qed.
Lemma lem4372322 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term6 _104960 _104961 f s) = (term19 _104960 _104961 f s).
Proof. exact (MK_COMB (@lem4372321 _104960 _104961 f s) (@lem4372316 _104960 _104961 f s)). Qed.
Lemma lem4372323 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term5 _104960 _104961 f s) = ((term9 _104960 _104961 s f) = (term20 _104960 _104961 f s)).
Proof. exact (eq_refl (term5 _104960 _104961 f s)). Qed.
Lemma lem4372324 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4372325 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term21 _104960 _104961 f s) = (term22 _104960 _104961 f s).
Proof. exact (MK_COMB (@lem4372324) (@lem4372323 _104960 _104961 f s)). Qed.
Lemma lem4372326 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : ((term5 _104960 _104961 f s) = (term6 _104960 _104961 f s)) = (((term9 _104960 _104961 s f) = (term20 _104960 _104961 f s)) = (term19 _104960 _104961 f s)).
Proof. exact (MK_COMB (@lem4372325 _104960 _104961 f s) (@lem4372322 _104960 _104961 f s)). Qed.
Lemma lem4372327 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : ((term9 _104960 _104961 s f) = (term20 _104960 _104961 f s)) = (term19 _104960 _104961 f s).
Proof. exact (EQ_MP (@lem4372326 _104960 _104961 f s) (@lem4372313 _104960 _104961 f s)). Qed.
Lemma lem4372328 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term19 _104960 _104961 f s) = ((term9 _104960 _104961 s f) = (term20 _104960 _104961 f s)).
Proof. exact (SYM (@lem4372327 _104960 _104961 f s)). Qed.
