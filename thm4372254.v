Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4372254_term_abbrevs.
Require Import thm13473_spec.
Lemma lem4372237 {_104907 _104908 : Type'} (_474 : type1210 _104907 _104908) (_475 : Prop) (_476 : type324 _104907 _104908) (_477 : type1210 _104907 _104908) : (term0 _104907 _104908 _476 _475 _474 _477) = (term1 _104907 _104908 _474 _475 _476 _477).
Proof. exact (@lem13473 (type1210 _104907 _104908) _474 _475 _476 _477). Qed.
Lemma lem4372238 {_104907 _104908 : Type'} (_474 : type1210 _104907 _104908) (_475 : Prop) (f : type686 _104907) (g : type686 _104908) (_477 : type1210 _104907 _104908) : (term2 _104907 _104908 f g _475 _474 _477) = (term3 _104907 _104908 _474 _475 f g _477).
Proof. exact (@lem4372237 _104907 _104908 _474 _475 (term4 _104907 _104908 f g) _477). Qed.
Lemma lem4372239 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term5 _104907 _104908 f g) = (term6 _104907 _104908 f g).
Proof. exact (@lem4372238 _104907 _104908 (term7 _104907 _104908 f) (g = (@EMPTY (_104908 -> Prop))) f g (term8 _104907 _104908 f g)). Qed.
Lemma lem4372240 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term9 _104907 _104908 f g) = ((term10 _104907 _104908 f g) = (term8 _104907 _104908 f g)).
Proof. exact (eq_refl (term9 _104907 _104908 f g)). Qed.
Lemma lem4372241 {_104908 : Type'} (g : type686 _104908) : (term11 _104908 g) = (term11 _104908 g).
Proof. exact (eq_refl (term11 _104908 g)). Qed.
Lemma lem4372242 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term12 _104907 _104908 f g) = (term13 _104907 _104908 f g).
Proof. exact (MK_COMB (@lem4372241 _104908 g) (@lem4372240 _104907 _104908 f g)). Qed.
Lemma lem4372243 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term14 _104907 _104908 g f) = ((term10 _104907 _104908 f g) = (term7 _104907 _104908 f)).
Proof. exact (eq_refl (term14 _104907 _104908 g f)). Qed.
Lemma lem4372244 {_104908 : Type'} (g : type686 _104908) : (term15 _104908 g) = (term15 _104908 g).
Proof. exact (eq_refl (term15 _104908 g)). Qed.
Lemma lem4372245 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term16 _104907 _104908 g f) = (term17 _104907 _104908 g f).
Proof. exact (MK_COMB (@lem4372244 _104908 g) (@lem4372243 _104907 _104908 g f)). Qed.
Lemma lem4372246 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4372247 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term18 _104907 _104908 g f) = (term19 _104907 _104908 g f).
Proof. exact (MK_COMB (@lem4372246) (@lem4372245 _104907 _104908 g f)). Qed.
Lemma lem4372248 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term6 _104907 _104908 f g) = (term20 _104907 _104908 f g).
Proof. exact (MK_COMB (@lem4372247 _104907 _104908 g f) (@lem4372242 _104907 _104908 f g)). Qed.
Lemma lem4372249 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term5 _104907 _104908 f g) = ((term10 _104907 _104908 f g) = (term21 _104907 _104908 f g)).
Proof. exact (eq_refl (term5 _104907 _104908 f g)). Qed.
Lemma lem4372250 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4372251 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term22 _104907 _104908 f g) = (term23 _104907 _104908 f g).
Proof. exact (MK_COMB (@lem4372250) (@lem4372249 _104907 _104908 f g)). Qed.
Lemma lem4372252 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : ((term5 _104907 _104908 f g) = (term6 _104907 _104908 f g)) = (((term10 _104907 _104908 f g) = (term21 _104907 _104908 f g)) = (term20 _104907 _104908 f g)).
Proof. exact (MK_COMB (@lem4372251 _104907 _104908 f g) (@lem4372248 _104907 _104908 f g)). Qed.
Lemma lem4372253 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : ((term10 _104907 _104908 f g) = (term21 _104907 _104908 f g)) = (term20 _104907 _104908 f g).
Proof. exact (EQ_MP (@lem4372252 _104907 _104908 f g) (@lem4372239 _104907 _104908 f g)). Qed.
Lemma lem4372254 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term20 _104907 _104908 f g) = ((term10 _104907 _104908 f g) = (term21 _104907 _104908 f g)).
Proof. exact (SYM (@lem4372253 _104907 _104908 f g)). Qed.
