Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4380502_term_abbrevs.
Require Import thm4372328_spec.
Require Import thm4372329_spec.
Require Import thm4372346_spec.
Require Import thm4373533_spec.
Require Import thm4373817_spec.
Require Import thm4377358_spec.
Require Import thm4378811_spec.
Lemma lem4380493 {_104960 _104961 : Type'} (s : _104960 -> Prop) (f : type686 _104961) (h1 : term0 _104961 f) : (term1 _104960 _104961 s f) = (term2 _104960 _104961 f s).
Proof. exact (EQ_MP (@lem4373817 _104960 _104961 f s) (@lem4378811 _104960 _104961 s f h1)). Qed.
Lemma lem4380494 {_104960 _104961 : Type'} (s : _104960 -> Prop) (f : type686 _104961) (h1 : term0 _104961 f) : (term0 _104961 f) = ((term1 _104960 _104961 s f) = (term2 _104960 _104961 f s)).
Proof. exact (prop_ext (fun h2 : term0 _104961 f => @lem4380493 _104960 _104961 s f h1) (fun h2 : (term1 _104960 _104961 s f) = (term2 _104960 _104961 f s) => @lem4372346 _104961 f h1)). Qed.
Lemma lem4380495 {_104960 _104961 : Type'} (s : _104960 -> Prop) (f : type686 _104961) (h1 : term0 _104961 f) : (term1 _104960 _104961 s f) = (term2 _104960 _104961 f s).
Proof. exact (EQ_MP (@lem4380494 _104960 _104961 s f h1) (@lem4372346 _104961 f h1)). Qed.
Lemma lem4380496 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : term3 _104960 _104961 f s.
Proof. exact (fun h0 : term0 _104961 f => @lem4380495 _104960 _104961 s f h0). Qed.
Lemma lem4380497 {_104960 _104961 : Type'} (s : _104960 -> Prop) (f : type686 _104961) (h1 : f = (@EMPTY (_104961 -> Prop))) : (term1 _104960 _104961 s f) = (@CROSS _104961 _104960 s (@UNIV _104961)).
Proof. exact (EQ_MP (@lem4373533 _104960 _104961 s f h1) (@lem4377358 _104960 _104961 s f h1)). Qed.
Lemma lem4380498 {_104960 _104961 : Type'} (s : _104960 -> Prop) (f : type686 _104961) (h1 : f = (@EMPTY (_104961 -> Prop))) : (f = (@EMPTY (_104961 -> Prop))) = ((term1 _104960 _104961 s f) = (@CROSS _104961 _104960 s (@UNIV _104961))).
Proof. exact (prop_ext (fun h2 : f = (@EMPTY (_104961 -> Prop)) => @lem4380497 _104960 _104961 s f h1) (fun h2 : (term1 _104960 _104961 s f) = (@CROSS _104961 _104960 s (@UNIV _104961)) => @lem4372329 _104961 f h1)). Qed.
Lemma lem4380499 {_104960 _104961 : Type'} (s : _104960 -> Prop) (f : type686 _104961) (h1 : f = (@EMPTY (_104961 -> Prop))) : (term1 _104960 _104961 s f) = (@CROSS _104961 _104960 s (@UNIV _104961)).
Proof. exact (EQ_MP (@lem4380498 _104960 _104961 s f h1) (@lem4372329 _104961 f h1)). Qed.
Lemma lem4380500 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : term4 _104960 _104961 f s.
Proof. exact (fun h0 : f = (@EMPTY (_104961 -> Prop)) => @lem4380499 _104960 _104961 s f h0). Qed.
Lemma lem4380501 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : term5 _104960 _104961 f s.
Proof. exact (conj (@lem4380500 _104960 _104961 f s) (@lem4380496 _104960 _104961 f s)). Qed.
Lemma lem4380502 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term1 _104960 _104961 s f) = (term6 _104960 _104961 f s).
Proof. exact (EQ_MP (@lem4372328 _104960 _104961 f s) (@lem4380501 _104960 _104961 f s)). Qed.
