Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm8049005_term_abbrevs.
Require Import thm13473_spec.
Lemma lem8048988 {_143007 _143008 _143009 : Type'} (_474 : type16 _143007 _143008 _143009) (_475 : Prop) (_476 : type51 _143007 _143008 _143009) (_477 : type16 _143007 _143008 _143009) : (term0 _143007 _143008 _143009 _476 _475 _474 _477) = (term1 _143007 _143008 _143009 _474 _475 _476 _477).
Proof. exact (@lem13473 (type16 _143007 _143008 _143009) _474 _475 _476 _477). Qed.
Lemma lem8048989 {_143007 _143008 _143009 : Type'} (_474 : type16 _143007 _143008 _143009) (_475 : Prop) (s : type24 _143007 _143008) (f : type56 _143007 _143009) (_477 : type16 _143007 _143008 _143009) : (term2 _143007 _143008 _143009 s f _475 _474 _477) = (term3 _143007 _143008 _143009 _474 _475 s f _477).
Proof. exact (@lem8048988 _143007 _143008 _143009 _474 _475 (term4 _143007 _143008 _143009 s f) _477). Qed.
Lemma lem8048990 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term5 _143007 _143008 _143009 f s) = (term6 _143007 _143008 _143009 f s).
Proof. exact (@lem8048989 _143007 _143008 _143009 (@PCROSS _143007 _143008 _143009 s (@UNIV (cart _143007 _143009))) (f = (@EMPTY ((cart _143007 _143009) -> Prop))) s f (term7 _143007 _143008 _143009 f s)). Qed.
Lemma lem8048991 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term8 _143007 _143008 _143009 f s) = ((term9 _143007 _143008 _143009 s f) = (term7 _143007 _143008 _143009 f s)).
Proof. exact (eq_refl (term8 _143007 _143008 _143009 f s)). Qed.
Lemma lem8048992 {_143007 _143009 : Type'} (f : type56 _143007 _143009) : (term10 _143007 _143009 f) = (term10 _143007 _143009 f).
Proof. exact (eq_refl (term10 _143007 _143009 f)). Qed.
Lemma lem8048993 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term11 _143007 _143008 _143009 f s) = (term12 _143007 _143008 _143009 f s).
Proof. exact (MK_COMB (@lem8048992 _143007 _143009 f) (@lem8048991 _143007 _143008 _143009 f s)). Qed.
Lemma lem8048994 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term13 _143007 _143008 _143009 f s) = ((term9 _143007 _143008 _143009 s f) = (@PCROSS _143007 _143008 _143009 s (@UNIV (cart _143007 _143009)))).
Proof. exact (eq_refl (term13 _143007 _143008 _143009 f s)). Qed.
Lemma lem8048995 {_143007 _143009 : Type'} (f : type56 _143007 _143009) : (term14 _143007 _143009 f) = (term14 _143007 _143009 f).
Proof. exact (eq_refl (term14 _143007 _143009 f)). Qed.
Lemma lem8048996 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term15 _143007 _143008 _143009 f s) = (term16 _143007 _143008 _143009 f s).
Proof. exact (MK_COMB (@lem8048995 _143007 _143009 f) (@lem8048994 _143007 _143008 _143009 f s)). Qed.
Lemma lem8048997 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8048998 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term17 _143007 _143008 _143009 f s) = (term18 _143007 _143008 _143009 f s).
Proof. exact (MK_COMB (@lem8048997) (@lem8048996 _143007 _143008 _143009 f s)). Qed.
Lemma lem8048999 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term6 _143007 _143008 _143009 f s) = (term19 _143007 _143008 _143009 f s).
Proof. exact (MK_COMB (@lem8048998 _143007 _143008 _143009 f s) (@lem8048993 _143007 _143008 _143009 f s)). Qed.
Lemma lem8049000 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term5 _143007 _143008 _143009 f s) = ((term9 _143007 _143008 _143009 s f) = (term20 _143007 _143008 _143009 f s)).
Proof. exact (eq_refl (term5 _143007 _143008 _143009 f s)). Qed.
Lemma lem8049001 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8049002 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term21 _143007 _143008 _143009 f s) = (term22 _143007 _143008 _143009 f s).
Proof. exact (MK_COMB (@lem8049001) (@lem8049000 _143007 _143008 _143009 f s)). Qed.
Lemma lem8049003 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : ((term5 _143007 _143008 _143009 f s) = (term6 _143007 _143008 _143009 f s)) = (((term9 _143007 _143008 _143009 s f) = (term20 _143007 _143008 _143009 f s)) = (term19 _143007 _143008 _143009 f s)).
Proof. exact (MK_COMB (@lem8049002 _143007 _143008 _143009 f s) (@lem8048999 _143007 _143008 _143009 f s)). Qed.
Lemma lem8049004 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : ((term9 _143007 _143008 _143009 s f) = (term20 _143007 _143008 _143009 f s)) = (term19 _143007 _143008 _143009 f s).
Proof. exact (EQ_MP (@lem8049003 _143007 _143008 _143009 f s) (@lem8048990 _143007 _143008 _143009 f s)). Qed.
Lemma lem8049005 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term19 _143007 _143008 _143009 f s) = ((term9 _143007 _143008 _143009 s f) = (term20 _143007 _143008 _143009 f s)).
Proof. exact (SYM (@lem8049004 _143007 _143008 _143009 f s)). Qed.