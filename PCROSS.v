Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PCROSS_term_abbrevs.
Lemma lem8003706 {A M N : Type'} : (@PCROSS A M N) = (term0 A M N).
Proof. exact (@PCROSS_def A M N). Qed.
Lemma lem8003707 {A M : Type'} (_105619 : type24 A M) : _105619 = _105619.
Proof. exact (eq_refl _105619). Qed.
Lemma lem8003708 {A M N : Type'} (_105619 : type24 A M) : (@PCROSS A M N _105619) = (term1 A M N _105619).
Proof. exact (MK_COMB (@lem8003706 A M N) (@lem8003707 A M _105619)). Qed.
Lemma lem8003709 {A M N : Type'} (_105619 : type24 A M) : (term1 A M N _105619) = (term2 A M N _105619).
Proof. exact (eq_refl (term1 A M N _105619)). Qed.
Lemma lem8003710 {A M N : Type'} (_105619 : type24 A M) : (@PCROSS A M N _105619) = (term2 A M N _105619).
Proof. exact (TRANS (@lem8003708 A M N _105619) (@lem8003709 A M N _105619)). Qed.
Lemma lem8003711 {A N : Type'} (_105620 : type24 A N) : _105620 = _105620.
Proof. exact (eq_refl _105620). Qed.
Lemma lem8003712 {A M N : Type'} (_105619 : type24 A M) (_105620 : type24 A N) : (@PCROSS A M N _105619 _105620) = (term3 A M N _105619 _105620).
Proof. exact (MK_COMB (@lem8003710 A M N _105619) (@lem8003711 A N _105620)). Qed.
Lemma lem8003713 {A M N : Type'} (_105619 : type24 A M) (_105620 : type24 A N) : (term3 A M N _105619 _105620) = (term4 A M N _105619 _105620).
Proof. exact (eq_refl (term3 A M N _105619 _105620)). Qed.
Lemma lem8003714 {A M N : Type'} (_105619 : type24 A M) (_105620 : type24 A N) : (@PCROSS A M N _105619 _105620) = (term4 A M N _105619 _105620).
Proof. exact (TRANS (@lem8003712 A M N _105619 _105620) (@lem8003713 A M N _105619 _105620)). Qed.
Lemma lem8003715 {A M N : Type'} (_105619 : type24 A M) : term5 A M N _105619.
Proof. exact (fun _105620 : type24 A N => @lem8003714 A M N _105619 _105620). Qed.
Lemma lem8003716 {A M N : Type'} : term6 A M N.
Proof. exact (fun _105619 : type24 A M => @lem8003715 A M N _105619). Qed.
Lemma lem8003717 {A M N : Type'} (_105619 : type24 A M) : term7 A M N _105619.
Proof. exact (@lem8003716 A M N _105619). Qed.
Lemma lem8003718 {A M N : Type'} (_105619 : type24 A M) : (term7 A M N _105619) = (term5 A M N _105619).
Proof. exact (eq_refl (term7 A M N _105619)). Qed.
Lemma lem8003719 {A M N : Type'} (_105619 : type24 A M) : term5 A M N _105619.
Proof. exact (EQ_MP (@lem8003718 A M N _105619) (@lem8003717 A M N _105619)). Qed.
Lemma lem8003720 {A M N : Type'} (_105619 : type24 A M) (_105620 : type24 A N) : term8 A M N _105619 _105620.
Proof. exact (@lem8003719 A M N _105619 _105620). Qed.
Lemma lem8003721 {A M N : Type'} (_105619 : type24 A M) (_105620 : type24 A N) : (term8 A M N _105619 _105620) = ((@PCROSS A M N _105619 _105620) = (term4 A M N _105619 _105620)).
Proof. exact (eq_refl (term8 A M N _105619 _105620)). Qed.
Lemma lem8003722 {A M N : Type'} (_105619 : type24 A M) (_105620 : type24 A N) : (@PCROSS A M N _105619 _105620) = (term4 A M N _105619 _105620).
Proof. exact (EQ_MP (@lem8003721 A M N _105619 _105620) (@lem8003720 A M N _105619 _105620)). Qed.
Lemma lem8003765 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (@PCROSS A M N s t) = (term4 A M N s t).
Proof. exact (@lem8003722 A M N s t). Qed.
Lemma lem8003766 {A M N : Type'} (s : type24 A M) : term5 A M N s.
Proof. exact (fun t : type24 A N => @lem8003765 A M N s t). Qed.
Lemma lem8003767 {A M N : Type'} : term6 A M N.
Proof. exact (fun s : type24 A M => @lem8003766 A M N s). Qed.
