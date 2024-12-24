Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNION_term_abbrevs.
Lemma lem3188283 {A : Type'} : (@UNION A) = (term0 A).
Proof. exact (@UNION_def A). Qed.
Lemma lem3188284 {A : Type'} (_32751 : A -> Prop) : _32751 = _32751.
Proof. exact (eq_refl _32751). Qed.
Lemma lem3188285 {A : Type'} (_32751 : A -> Prop) : (@UNION A _32751) = (term1 A _32751).
Proof. exact (MK_COMB (@lem3188283 A) (@lem3188284 A _32751)). Qed.
Lemma lem3188286 {A : Type'} (_32751 : A -> Prop) : (term1 A _32751) = (term2 A _32751).
Proof. exact (eq_refl (term1 A _32751)). Qed.
Lemma lem3188287 {A : Type'} (_32751 : A -> Prop) : (@UNION A _32751) = (term2 A _32751).
Proof. exact (TRANS (@lem3188285 A _32751) (@lem3188286 A _32751)). Qed.
Lemma lem3188288 {A : Type'} (_32752 : A -> Prop) : _32752 = _32752.
Proof. exact (eq_refl _32752). Qed.
Lemma lem3188289 {A : Type'} (_32751 : A -> Prop) (_32752 : A -> Prop) : (@UNION A _32751 _32752) = (term3 A _32751 _32752).
Proof. exact (MK_COMB (@lem3188287 A _32751) (@lem3188288 A _32752)). Qed.
Lemma lem3188290 {A : Type'} (_32751 : A -> Prop) (_32752 : A -> Prop) : (term3 A _32751 _32752) = (term4 A _32751 _32752).
Proof. exact (eq_refl (term3 A _32751 _32752)). Qed.
Lemma lem3188291 {A : Type'} (_32751 : A -> Prop) (_32752 : A -> Prop) : (@UNION A _32751 _32752) = (term4 A _32751 _32752).
Proof. exact (TRANS (@lem3188289 A _32751 _32752) (@lem3188290 A _32751 _32752)). Qed.
Lemma lem3188292 {A : Type'} (_32751 : A -> Prop) : term5 A _32751.
Proof. exact (fun _32752 : A -> Prop => @lem3188291 A _32751 _32752). Qed.
Lemma lem3188293 {A : Type'} : term6 A.
Proof. exact (fun _32751 : A -> Prop => @lem3188292 A _32751). Qed.
Lemma lem3188294 {A : Type'} (_32751 : A -> Prop) : term7 A _32751.
Proof. exact (@lem3188293 A _32751). Qed.
Lemma lem3188295 {A : Type'} (_32751 : A -> Prop) : (term7 A _32751) = (term5 A _32751).
Proof. exact (eq_refl (term7 A _32751)). Qed.
Lemma lem3188296 {A : Type'} (_32751 : A -> Prop) : term5 A _32751.
Proof. exact (EQ_MP (@lem3188295 A _32751) (@lem3188294 A _32751)). Qed.
Lemma lem3188297 {A : Type'} (_32751 : A -> Prop) (_32752 : A -> Prop) : term8 A _32751 _32752.
Proof. exact (@lem3188296 A _32751 _32752). Qed.
Lemma lem3188298 {A : Type'} (_32751 : A -> Prop) (_32752 : A -> Prop) : (term8 A _32751 _32752) = ((@UNION A _32751 _32752) = (term4 A _32751 _32752)).
Proof. exact (eq_refl (term8 A _32751 _32752)). Qed.
Lemma lem3188299 {A : Type'} (_32751 : A -> Prop) (_32752 : A -> Prop) : (@UNION A _32751 _32752) = (term4 A _32751 _32752).
Proof. exact (EQ_MP (@lem3188298 A _32751 _32752) (@lem3188297 A _32751 _32752)). Qed.
Lemma lem3188342 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@UNION A s t) = (term4 A s t).
Proof. exact (@lem3188299 A s t). Qed.
Lemma lem3188343 {A : Type'} (s : A -> Prop) : term5 A s.
Proof. exact (fun t : A -> Prop => @lem3188342 A s t). Qed.
Lemma lem3188344 {A : Type'} : term6 A.
Proof. exact (fun s : A -> Prop => @lem3188343 A s). Qed.
