Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4372172_term_abbrevs.
Require Import thm13473_spec.
Lemma lem4372155 {_104907 _104908 : Type'} (_474 : type1210 _104907 _104908) (_475 : Prop) (_476 : type324 _104907 _104908) (_477 : type1210 _104907 _104908) : (term0 _104907 _104908 _476 _475 _474 _477) = (term1 _104907 _104908 _474 _475 _476 _477).
Proof. exact (@lem13473 (type1210 _104907 _104908) _474 _475 _476 _477). Qed.
Lemma lem4372156 {_104907 _104908 : Type'} (_474 : type1210 _104907 _104908) (_475 : Prop) (f : type686 _104907) (g : type686 _104908) (_477 : type1210 _104907 _104908) : (term2 _104907 _104908 f g _475 _474 _477) = (term3 _104907 _104908 _474 _475 f g _477).
Proof. exact (@lem4372155 _104907 _104908 _474 _475 (term4 _104907 _104908 f g) _477). Qed.
Lemma lem4372157 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term5 _104907 _104908 f g) = (term6 _104907 _104908 f g).
Proof. exact (@lem4372156 _104907 _104908 (term7 _104907 _104908 g) (f = (@EMPTY (_104907 -> Prop))) f g (term8 _104907 _104908 f g)). Qed.
Lemma lem4372158 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term9 _104907 _104908 f g) = ((term10 _104907 _104908 f g) = (term8 _104907 _104908 f g)).
Proof. exact (eq_refl (term9 _104907 _104908 f g)). Qed.
Lemma lem4372159 {_104907 : Type'} (f : type686 _104907) : (term11 _104907 f) = (term11 _104907 f).
Proof. exact (eq_refl (term11 _104907 f)). Qed.
Lemma lem4372160 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term12 _104907 _104908 f g) = (term13 _104907 _104908 f g).
Proof. exact (MK_COMB (@lem4372159 _104907 f) (@lem4372158 _104907 _104908 f g)). Qed.
Lemma lem4372161 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term14 _104907 _104908 f g) = ((term10 _104907 _104908 f g) = (term7 _104907 _104908 g)).
Proof. exact (eq_refl (term14 _104907 _104908 f g)). Qed.
Lemma lem4372162 {_104907 : Type'} (f : type686 _104907) : (term15 _104907 f) = (term15 _104907 f).
Proof. exact (eq_refl (term15 _104907 f)). Qed.
Lemma lem4372163 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term16 _104907 _104908 f g) = (term17 _104907 _104908 f g).
Proof. exact (MK_COMB (@lem4372162 _104907 f) (@lem4372161 _104907 _104908 f g)). Qed.
Lemma lem4372164 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4372165 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term18 _104907 _104908 f g) = (term19 _104907 _104908 f g).
Proof. exact (MK_COMB (@lem4372164) (@lem4372163 _104907 _104908 f g)). Qed.
Lemma lem4372166 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term6 _104907 _104908 f g) = (term20 _104907 _104908 f g).
Proof. exact (MK_COMB (@lem4372165 _104907 _104908 f g) (@lem4372160 _104907 _104908 f g)). Qed.
Lemma lem4372167 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term5 _104907 _104908 f g) = ((term10 _104907 _104908 f g) = (term21 _104907 _104908 f g)).
Proof. exact (eq_refl (term5 _104907 _104908 f g)). Qed.
Lemma lem4372168 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4372169 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term22 _104907 _104908 f g) = (term23 _104907 _104908 f g).
Proof. exact (MK_COMB (@lem4372168) (@lem4372167 _104907 _104908 f g)). Qed.
Lemma lem4372170 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : ((term5 _104907 _104908 f g) = (term6 _104907 _104908 f g)) = (((term10 _104907 _104908 f g) = (term21 _104907 _104908 f g)) = (term20 _104907 _104908 f g)).
Proof. exact (MK_COMB (@lem4372169 _104907 _104908 f g) (@lem4372166 _104907 _104908 f g)). Qed.
Lemma lem4372171 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : ((term10 _104907 _104908 f g) = (term21 _104907 _104908 f g)) = (term20 _104907 _104908 f g).
Proof. exact (EQ_MP (@lem4372170 _104907 _104908 f g) (@lem4372157 _104907 _104908 f g)). Qed.
Lemma lem4372172 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term20 _104907 _104908 f g) = ((term10 _104907 _104908 f g) = (term21 _104907 _104908 f g)).
Proof. exact (SYM (@lem4372171 _104907 _104908 f g)). Qed.
