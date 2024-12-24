Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7614851_term_abbrevs.
Require Import thm0_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem7614826 {A : Type'} (t : Prop) : (term0 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem7614827 {A B : Type'} (t : Prop) : (term1 A B t) = t.
Proof. exact (@lem7614826 (type35 A B) t). Qed.
Lemma lem7614828 {A B : Type'} : (term2 A B) = True.
Proof. exact (@lem7614827 A B True). Qed.
Lemma lem7614829 {A B : Type'} : True = (term2 A B).
Proof. exact (SYM (@lem7614828 A B)). Qed.
Lemma lem7614830 {A B : Type'} : term2 A B.
Proof. exact (EQ_MP (@lem7614829 A B) (@lem0)). Qed.
Lemma lem7614832 {A : Type'} : (@ex A) = (term3 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem7614833 {A B : Type'} : (@ex ((finite_image B) -> A)) = (term4 A B).
Proof. exact (@lem7614832 (type35 A B)). Qed.
Lemma lem7614834 {A B : Type'} : (term5 A B) = (term5 A B).
Proof. exact (eq_refl (term5 A B)). Qed.
Lemma lem7614835 {A B : Type'} : (term2 A B) = (term6 A B).
Proof. exact (MK_COMB (@lem7614833 A B) (@lem7614834 A B)). Qed.
Lemma lem7614836 {A B : Type'} : (term6 A B) = (term7 A B).
Proof. exact (eq_refl (term6 A B)). Qed.
Lemma lem7614837 {A B : Type'} : (term2 A B) = (term7 A B).
Proof. exact (TRANS (@lem7614835 A B) (@lem7614836 A B)). Qed.
Lemma lem7614838 {A B : Type'} : term7 A B.
Proof. exact (EQ_MP (@lem7614837 A B) (@lem7614830 A B)). Qed.
Lemma lem7614839 {A B : Type'} (a : cart A B) : (term8 A B a) = a.
Proof. exact (@axiom_29 A B a). Qed.
Lemma lem7614840 {A B : Type'} (r : type35 A B) : (term9 A B r) = ((term10 A B r) = r).
Proof. exact (@axiom_30 A B r). Qed.
Lemma lem7614843 {A B : Type'} (r : type35 A B) : (term9 A B r) = True.
Proof. exact (eq_refl (term9 A B r)). Qed.
Lemma lem7614844 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7614845 {A B : Type'} (r : type35 A B) : (term11 A B r) = (@eq Prop True).
Proof. exact (MK_COMB (@lem7614844) (@lem7614843 A B r)). Qed.
Lemma lem7614846 {A B : Type'} (r : type35 A B) : ((term10 A B r) = r) = ((term10 A B r) = r).
Proof. exact (eq_refl ((term10 A B r) = r)). Qed.
Lemma lem7614847 {A B : Type'} (r : type35 A B) : ((term9 A B r) = ((term10 A B r) = r)) = (True = ((term10 A B r) = r)).
Proof. exact (MK_COMB (@lem7614845 A B r) (@lem7614846 A B r)). Qed.
Lemma lem7614848 {A B : Type'} (r : type35 A B) : True = ((term10 A B r) = r).
Proof. exact (EQ_MP (@lem7614847 A B r) (@lem7614840 A B r)). Qed.
Lemma lem7614849 {A B : Type'} : term12 A B.
Proof. exact (fun r : type35 A B => @lem7614848 A B r). Qed.
Lemma lem7614850 {A B : Type'} : term13 A B.
Proof. exact (fun a : cart A B => @lem7614839 A B a). Qed.
Lemma lem7614851 {A B : Type'} : term14 A B.
Proof. exact (conj (@lem7614850 A B) (@lem7614849 A B)). Qed.
