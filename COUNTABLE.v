Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import COUNTABLE_term_abbrevs.
Lemma lem5132705 {_115106 : Type'} : (@COUNTABLE _115106) = (term0 _115106).
Proof. exact (@COUNTABLE_def _115106). Qed.
Lemma lem5132706 {_115106 : Type'} (_67040 : _115106 -> Prop) : _67040 = _67040.
Proof. exact (eq_refl _67040). Qed.
Lemma lem5132707 {_115106 : Type'} (_67040 : _115106 -> Prop) : (@COUNTABLE _115106 _67040) = (term1 _115106 _67040).
Proof. exact (MK_COMB (@lem5132705 _115106) (@lem5132706 _115106 _67040)). Qed.
Lemma lem5132708 {_115106 : Type'} (_67040 : _115106 -> Prop) : (term1 _115106 _67040) = (@ge_c _115106 nat (@UNIV nat) _67040).
Proof. exact (eq_refl (term1 _115106 _67040)). Qed.
Lemma lem5132709 {_115106 : Type'} (_67040 : _115106 -> Prop) : (@COUNTABLE _115106 _67040) = (@ge_c _115106 nat (@UNIV nat) _67040).
Proof. exact (TRANS (@lem5132707 _115106 _67040) (@lem5132708 _115106 _67040)). Qed.
Lemma lem5132710 {_115106 : Type'} : term2 _115106.
Proof. exact (fun _67040 : _115106 -> Prop => @lem5132709 _115106 _67040). Qed.
Lemma lem5132711 {_115106 : Type'} (_67040 : _115106 -> Prop) : term3 _115106 _67040.
Proof. exact (@lem5132710 _115106 _67040). Qed.
Lemma lem5132712 {_115106 : Type'} (_67040 : _115106 -> Prop) : (term3 _115106 _67040) = ((@COUNTABLE _115106 _67040) = (@ge_c _115106 nat (@UNIV nat) _67040)).
Proof. exact (eq_refl (term3 _115106 _67040)). Qed.
Lemma lem5132713 {_115106 : Type'} (_67040 : _115106 -> Prop) : (@COUNTABLE _115106 _67040) = (@ge_c _115106 nat (@UNIV nat) _67040).
Proof. exact (EQ_MP (@lem5132712 _115106 _67040) (@lem5132711 _115106 _67040)). Qed.
Lemma lem5132743 {_115106 : Type'} (t : _115106 -> Prop) : (@COUNTABLE _115106 t) = (@ge_c _115106 nat (@UNIV nat) t).
Proof. exact (@lem5132713 _115106 t). Qed.
Lemma lem5132744 {_115106 : Type'} : term2 _115106.
Proof. exact (fun t : _115106 -> Prop => @lem5132743 _115106 t). Qed.
