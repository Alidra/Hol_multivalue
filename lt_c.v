Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import lt_c_term_abbrevs.
Lemma lem5121982 {_114946 _114947 : Type'} : (@lt_c _114946 _114947) = (term0 _114946 _114947).
Proof. exact (@lt_c_def _114946 _114947). Qed.
Lemma lem5121983 {_114946 : Type'} (_66853 : _114946 -> Prop) : _66853 = _66853.
Proof. exact (eq_refl _66853). Qed.
Lemma lem5121984 {_114946 _114947 : Type'} (_66853 : _114946 -> Prop) : (@lt_c _114946 _114947 _66853) = (term1 _114946 _114947 _66853).
Proof. exact (MK_COMB (@lem5121982 _114946 _114947) (@lem5121983 _114946 _66853)). Qed.
Lemma lem5121985 {_114946 _114947 : Type'} (_66853 : _114946 -> Prop) : (term1 _114946 _114947 _66853) = (term2 _114946 _114947 _66853).
Proof. exact (eq_refl (term1 _114946 _114947 _66853)). Qed.
Lemma lem5121986 {_114946 _114947 : Type'} (_66853 : _114946 -> Prop) : (@lt_c _114946 _114947 _66853) = (term2 _114946 _114947 _66853).
Proof. exact (TRANS (@lem5121984 _114946 _114947 _66853) (@lem5121985 _114946 _114947 _66853)). Qed.
Lemma lem5121987 {_114947 : Type'} (_66854 : _114947 -> Prop) : _66854 = _66854.
Proof. exact (eq_refl _66854). Qed.
Lemma lem5121988 {_114946 _114947 : Type'} (_66853 : _114946 -> Prop) (_66854 : _114947 -> Prop) : (@lt_c _114946 _114947 _66853 _66854) = (term3 _114946 _114947 _66853 _66854).
Proof. exact (MK_COMB (@lem5121986 _114946 _114947 _66853) (@lem5121987 _114947 _66854)). Qed.
Lemma lem5121989 {_114946 _114947 : Type'} (_66854 : _114947 -> Prop) (_66853 : _114946 -> Prop) : (term3 _114946 _114947 _66853 _66854) = (term4 _114946 _114947 _66854 _66853).
Proof. exact (eq_refl (term3 _114946 _114947 _66853 _66854)). Qed.
Lemma lem5121990 {_114946 _114947 : Type'} (_66854 : _114947 -> Prop) (_66853 : _114946 -> Prop) : (@lt_c _114946 _114947 _66853 _66854) = (term4 _114946 _114947 _66854 _66853).
Proof. exact (TRANS (@lem5121988 _114946 _114947 _66853 _66854) (@lem5121989 _114946 _114947 _66854 _66853)). Qed.
Lemma lem5121991 {_114946 _114947 : Type'} (_66853 : _114946 -> Prop) : term5 _114946 _114947 _66853.
Proof. exact (fun _66854 : _114947 -> Prop => @lem5121990 _114946 _114947 _66854 _66853). Qed.
Lemma lem5121992 {_114946 _114947 : Type'} : term6 _114946 _114947.
Proof. exact (fun _66853 : _114946 -> Prop => @lem5121991 _114946 _114947 _66853). Qed.
Lemma lem5121993 {_114946 _114947 : Type'} (_66853 : _114946 -> Prop) : term7 _114946 _114947 _66853.
Proof. exact (@lem5121992 _114946 _114947 _66853). Qed.
Lemma lem5121994 {_114946 _114947 : Type'} (_66853 : _114946 -> Prop) : (term7 _114946 _114947 _66853) = (term5 _114946 _114947 _66853).
Proof. exact (eq_refl (term7 _114946 _114947 _66853)). Qed.
Lemma lem5121995 {_114946 _114947 : Type'} (_66853 : _114946 -> Prop) : term5 _114946 _114947 _66853.
Proof. exact (EQ_MP (@lem5121994 _114946 _114947 _66853) (@lem5121993 _114946 _114947 _66853)). Qed.
Lemma lem5121996 {_114946 _114947 : Type'} (_66853 : _114946 -> Prop) (_66854 : _114947 -> Prop) : term8 _114946 _114947 _66853 _66854.
Proof. exact (@lem5121995 _114946 _114947 _66853 _66854). Qed.
Lemma lem5121997 {_114946 _114947 : Type'} (_66854 : _114947 -> Prop) (_66853 : _114946 -> Prop) : (term8 _114946 _114947 _66853 _66854) = ((@lt_c _114946 _114947 _66853 _66854) = (term4 _114946 _114947 _66854 _66853)).
Proof. exact (eq_refl (term8 _114946 _114947 _66853 _66854)). Qed.
Lemma lem5121998 {_114946 _114947 : Type'} (_66854 : _114947 -> Prop) (_66853 : _114946 -> Prop) : (@lt_c _114946 _114947 _66853 _66854) = (term4 _114946 _114947 _66854 _66853).
Proof. exact (EQ_MP (@lem5121997 _114946 _114947 _66854 _66853) (@lem5121996 _114946 _114947 _66853 _66854)). Qed.
Lemma lem5122041 {_114946 _114947 : Type'} (t : _114947 -> Prop) (s : _114946 -> Prop) : (@lt_c _114946 _114947 s t) = (term4 _114946 _114947 t s).
Proof. exact (@lem5121998 _114946 _114947 t s). Qed.
Lemma lem5122042 {_114946 _114947 : Type'} (t : _114947 -> Prop) : term9 _114946 _114947 t.
Proof. exact (fun s : _114946 -> Prop => @lem5122041 _114946 _114947 t s). Qed.
Lemma lem5122043 {_114946 _114947 : Type'} : term10 _114946 _114947.
Proof. exact (fun t : _114947 -> Prop => @lem5122042 _114946 _114947 t). Qed.
