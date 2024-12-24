Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SHRINK_GROW_term_abbrevs.
Require Import REAL_SHRINK_GROW_EQ_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1823_spec.
Lemma lem2258687 (x : real) : term0 x.
Proof. exact (@lem2258686 x). Qed.
Lemma lem2258688 (x : real) : (term0 x) = (((term1 x) = x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2258697 (x : real) : ((term1 x) = x) = (term2 x).
Proof. exact (EQ_MP (@lem2258688 x) (@lem2258687 x)). Qed.
Lemma lem2258698 (x : real) : (term3 x) = (term3 x).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem2258699 (x : real) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem2258698 x) (@lem2258697 x)). Qed.
Lemma lem2258701 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem2258702 (x : real) : (term5 x) = True.
Proof. exact (@lem2258701 (term2 x)). Qed.
Lemma lem2258703 (x : real) : (term4 x) = True.
Proof. exact (TRANS (@lem2258699 x) (@lem2258702 x)). Qed.
Lemma lem2258704 : term6 = term7.
Proof. exact (fun_ext (fun x : real => @lem2258703 x)). Qed.
Lemma lem2258705 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2258706 : term8 = term9.
Proof. exact (MK_COMB (@lem2258705) (@lem2258704)). Qed.
Lemma lem2258708 {A : Type'} (t : Prop) : (term10 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2258709 (t : Prop) : (term11 t) = t.
Proof. exact (@lem2258708 real t). Qed.
Lemma lem2258710 : term9 = True.
Proof. exact (@lem2258709 True). Qed.
Lemma lem2258711 : term8 = True.
Proof. exact (TRANS (@lem2258706) (@lem2258710)). Qed.
Lemma lem2258712 : True = term8.
Proof. exact (SYM (@lem2258711)). Qed.
Lemma lem2258713 : term8.
Proof. exact (EQ_MP (@lem2258712) (@lem0)). Qed.
