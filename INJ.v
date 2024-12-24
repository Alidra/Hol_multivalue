Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INJ_term_abbrevs.
Lemma lem3200496 {A B : Type'} : (@INJ A B) = (term0 A B).
Proof. exact (@INJ_def A B). Qed.
Lemma lem3200497 {A B : Type'} (_32871 : A -> B) : _32871 = _32871.
Proof. exact (eq_refl _32871). Qed.
Lemma lem3200498 {A B : Type'} (_32871 : A -> B) : (@INJ A B _32871) = (term1 A B _32871).
Proof. exact (MK_COMB (@lem3200496 A B) (@lem3200497 A B _32871)). Qed.
Lemma lem3200499 {A B : Type'} (_32871 : A -> B) : (term1 A B _32871) = (term2 A B _32871).
Proof. exact (eq_refl (term1 A B _32871)). Qed.
Lemma lem3200500 {A B : Type'} (_32871 : A -> B) : (@INJ A B _32871) = (term2 A B _32871).
Proof. exact (TRANS (@lem3200498 A B _32871) (@lem3200499 A B _32871)). Qed.
Lemma lem3200501 {A : Type'} (_32872 : A -> Prop) : _32872 = _32872.
Proof. exact (eq_refl _32872). Qed.
Lemma lem3200502 {A B : Type'} (_32871 : A -> B) (_32872 : A -> Prop) : (@INJ A B _32871 _32872) = (term3 A B _32871 _32872).
Proof. exact (MK_COMB (@lem3200500 A B _32871) (@lem3200501 A _32872)). Qed.
Lemma lem3200503 {A B : Type'} (_32872 : A -> Prop) (_32871 : A -> B) : (term3 A B _32871 _32872) = (term4 A B _32872 _32871).
Proof. exact (eq_refl (term3 A B _32871 _32872)). Qed.
Lemma lem3200504 {A B : Type'} (_32872 : A -> Prop) (_32871 : A -> B) : (@INJ A B _32871 _32872) = (term4 A B _32872 _32871).
Proof. exact (TRANS (@lem3200502 A B _32871 _32872) (@lem3200503 A B _32872 _32871)). Qed.
Lemma lem3200505 {B : Type'} (_32873 : B -> Prop) : _32873 = _32873.
Proof. exact (eq_refl _32873). Qed.
Lemma lem3200506 {A B : Type'} (_32872 : A -> Prop) (_32871 : A -> B) (_32873 : B -> Prop) : (@INJ A B _32871 _32872 _32873) = (term5 A B _32872 _32871 _32873).
Proof. exact (MK_COMB (@lem3200504 A B _32872 _32871) (@lem3200505 B _32873)). Qed.
Lemma lem3200507 {A B : Type'} (_32873 : B -> Prop) (_32872 : A -> Prop) (_32871 : A -> B) : (term5 A B _32872 _32871 _32873) = (term6 A B _32873 _32872 _32871).
Proof. exact (eq_refl (term5 A B _32872 _32871 _32873)). Qed.
Lemma lem3200508 {A B : Type'} (_32873 : B -> Prop) (_32872 : A -> Prop) (_32871 : A -> B) : (@INJ A B _32871 _32872 _32873) = (term6 A B _32873 _32872 _32871).
Proof. exact (TRANS (@lem3200506 A B _32872 _32871 _32873) (@lem3200507 A B _32873 _32872 _32871)). Qed.
Lemma lem3200509 {A B : Type'} (_32872 : A -> Prop) (_32871 : A -> B) : term7 A B _32872 _32871.
Proof. exact (fun _32873 : B -> Prop => @lem3200508 A B _32873 _32872 _32871). Qed.
Lemma lem3200510 {A B : Type'} (_32871 : A -> B) : term8 A B _32871.
Proof. exact (fun _32872 : A -> Prop => @lem3200509 A B _32872 _32871). Qed.
Lemma lem3200511 {A B : Type'} : term9 A B.
Proof. exact (fun _32871 : A -> B => @lem3200510 A B _32871). Qed.
Lemma lem3200512 {A B : Type'} (_32871 : A -> B) : term10 A B _32871.
Proof. exact (@lem3200511 A B _32871). Qed.
Lemma lem3200513 {A B : Type'} (_32871 : A -> B) : (term10 A B _32871) = (term8 A B _32871).
Proof. exact (eq_refl (term10 A B _32871)). Qed.
Lemma lem3200514 {A B : Type'} (_32871 : A -> B) : term8 A B _32871.
Proof. exact (EQ_MP (@lem3200513 A B _32871) (@lem3200512 A B _32871)). Qed.
Lemma lem3200515 {A B : Type'} (_32871 : A -> B) (_32872 : A -> Prop) : term11 A B _32871 _32872.
Proof. exact (@lem3200514 A B _32871 _32872). Qed.
Lemma lem3200516 {A B : Type'} (_32872 : A -> Prop) (_32871 : A -> B) : (term11 A B _32871 _32872) = (term7 A B _32872 _32871).
Proof. exact (eq_refl (term11 A B _32871 _32872)). Qed.
Lemma lem3200517 {A B : Type'} (_32872 : A -> Prop) (_32871 : A -> B) : term7 A B _32872 _32871.
Proof. exact (EQ_MP (@lem3200516 A B _32872 _32871) (@lem3200515 A B _32871 _32872)). Qed.
Lemma lem3200518 {A B : Type'} (_32872 : A -> Prop) (_32871 : A -> B) (_32873 : B -> Prop) : term12 A B _32872 _32871 _32873.
Proof. exact (@lem3200517 A B _32872 _32871 _32873). Qed.
Lemma lem3200519 {A B : Type'} (_32873 : B -> Prop) (_32872 : A -> Prop) (_32871 : A -> B) : (term12 A B _32872 _32871 _32873) = ((@INJ A B _32871 _32872 _32873) = (term6 A B _32873 _32872 _32871)).
Proof. exact (eq_refl (term12 A B _32872 _32871 _32873)). Qed.
Lemma lem3200520 {A B : Type'} (_32873 : B -> Prop) (_32872 : A -> Prop) (_32871 : A -> B) : (@INJ A B _32871 _32872 _32873) = (term6 A B _32873 _32872 _32871).
Proof. exact (EQ_MP (@lem3200519 A B _32873 _32872 _32871) (@lem3200518 A B _32872 _32871 _32873)). Qed.
Lemma lem3200576 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (@INJ A B f s t) = (term6 A B t s f).
Proof. exact (@lem3200520 A B t s f). Qed.
Lemma lem3200577 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term13 A B t s.
Proof. exact (fun f : A -> B => @lem3200576 A B t s f). Qed.
Lemma lem3200578 {A B : Type'} (t : B -> Prop) : term14 A B t.
Proof. exact (fun s : A -> Prop => @lem3200577 A B t s). Qed.
Lemma lem3200579 {A B : Type'} : term15 A B.
Proof. exact (fun t : B -> Prop => @lem3200578 A B t). Qed.
