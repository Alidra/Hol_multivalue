Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTERSECTION_OF_term_abbrevs.
Lemma lem4842178 {A : Type'} : (@INTERSECTION_OF A) = (term0 A).
Proof. exact (@INTERSECTION_OF_def A). Qed.
Lemma lem4842179 {A : Type'} (_60044 : type180 A) : _60044 = _60044.
Proof. exact (eq_refl _60044). Qed.
Lemma lem4842180 {A : Type'} (_60044 : type180 A) : (@INTERSECTION_OF A _60044) = (term1 A _60044).
Proof. exact (MK_COMB (@lem4842178 A) (@lem4842179 A _60044)). Qed.
Lemma lem4842181 {A : Type'} (_60044 : type180 A) : (term1 A _60044) = (term2 A _60044).
Proof. exact (eq_refl (term1 A _60044)). Qed.
Lemma lem4842182 {A : Type'} (_60044 : type180 A) : (@INTERSECTION_OF A _60044) = (term2 A _60044).
Proof. exact (TRANS (@lem4842180 A _60044) (@lem4842181 A _60044)). Qed.
Lemma lem4842183 {A : Type'} (_60045 : type686 A) : _60045 = _60045.
Proof. exact (eq_refl _60045). Qed.
Lemma lem4842184 {A : Type'} (_60044 : type180 A) (_60045 : type686 A) : (@INTERSECTION_OF A _60044 _60045) = (term3 A _60044 _60045).
Proof. exact (MK_COMB (@lem4842182 A _60044) (@lem4842183 A _60045)). Qed.
Lemma lem4842185 {A : Type'} (_60044 : type180 A) (_60045 : type686 A) : (term3 A _60044 _60045) = (term4 A _60044 _60045).
Proof. exact (eq_refl (term3 A _60044 _60045)). Qed.
Lemma lem4842186 {A : Type'} (_60044 : type180 A) (_60045 : type686 A) : (@INTERSECTION_OF A _60044 _60045) = (term4 A _60044 _60045).
Proof. exact (TRANS (@lem4842184 A _60044 _60045) (@lem4842185 A _60044 _60045)). Qed.
Lemma lem4842187 {A : Type'} (_60044 : type180 A) : term5 A _60044.
Proof. exact (fun _60045 : type686 A => @lem4842186 A _60044 _60045). Qed.
Lemma lem4842188 {A : Type'} : term6 A.
Proof. exact (fun _60044 : type180 A => @lem4842187 A _60044). Qed.
Lemma lem4842189 {A : Type'} (_60044 : type180 A) : term7 A _60044.
Proof. exact (@lem4842188 A _60044). Qed.
Lemma lem4842190 {A : Type'} (_60044 : type180 A) : (term7 A _60044) = (term5 A _60044).
Proof. exact (eq_refl (term7 A _60044)). Qed.
Lemma lem4842191 {A : Type'} (_60044 : type180 A) : term5 A _60044.
Proof. exact (EQ_MP (@lem4842190 A _60044) (@lem4842189 A _60044)). Qed.
Lemma lem4842192 {A : Type'} (_60044 : type180 A) (_60045 : type686 A) : term8 A _60044 _60045.
Proof. exact (@lem4842191 A _60044 _60045). Qed.
Lemma lem4842193 {A : Type'} (_60044 : type180 A) (_60045 : type686 A) : (term8 A _60044 _60045) = ((@INTERSECTION_OF A _60044 _60045) = (term4 A _60044 _60045)).
Proof. exact (eq_refl (term8 A _60044 _60045)). Qed.
Lemma lem4842194 {A : Type'} (_60044 : type180 A) (_60045 : type686 A) : (@INTERSECTION_OF A _60044 _60045) = (term4 A _60044 _60045).
Proof. exact (EQ_MP (@lem4842193 A _60044 _60045) (@lem4842192 A _60044 _60045)). Qed.
Lemma lem4842237 {A : Type'} (P : type180 A) (Q : type686 A) : (@INTERSECTION_OF A P Q) = (term4 A P Q).
Proof. exact (@lem4842194 A P Q). Qed.
Lemma lem4842238 {A : Type'} (P : type180 A) : term5 A P.
Proof. exact (fun Q : type686 A => @lem4842237 A P Q). Qed.
Lemma lem4842239 {A : Type'} : term6 A.
Proof. exact (fun P : type180 A => @lem4842238 A P). Qed.
