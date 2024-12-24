Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import OUTL_term_abbrevs.
Require Import thm1068183_spec.
Require Import thm1068509_spec.
Lemma lem1068510 {A B : Type'} : (term0 A B) = (term1 A B).
Proof. exact (eq_refl (term0 A B)). Qed.
Lemma lem1068511 {A B : Type'} : term1 A B.
Proof. exact (EQ_MP (@lem1068510 A B) (@lem1068183 A B)). Qed.
Lemma lem1068512 {A B : Type'} : term2 A B.
Proof. exact (@lem1068511 A B term3). Qed.
Lemma lem1068513 {A B : Type'} : (term2 A B) = (term4 A B).
Proof. exact (eq_refl (term2 A B)). Qed.
Lemma lem1068514 {A B : Type'} : term4 A B.
Proof. exact (EQ_MP (@lem1068513 A B) (@lem1068512 A B)). Qed.
Lemma lem1068515 {A B : Type'} (h1 : (@OUTL A B) = (term5 A B)) : (@OUTL A B) = (term5 A B).
Proof. exact (h1). Qed.
Lemma lem1068516 {A B : Type'} (h1 : (@OUTL A B) = (term5 A B)) : (term5 A B) = (@OUTL A B).
Proof. exact (SYM (@lem1068515 A B h1)). Qed.
Lemma lem1068517 {A B : Type'} (h1 : (term5 A B) = (@OUTL A B)) : (term5 A B) = (@OUTL A B).
Proof. exact (h1). Qed.
Lemma lem1068518 {A B : Type'} (h1 : (term5 A B) = (@OUTL A B)) : (@OUTL A B) = (term5 A B).
Proof. exact (SYM (@lem1068517 A B h1)). Qed.
Lemma lem1068519 {A B : Type'} : ((@OUTL A B) = (term5 A B)) = ((term5 A B) = (@OUTL A B)).
Proof. exact (prop_ext (fun h1 : (@OUTL A B) = (term5 A B) => @lem1068516 A B h1) (fun h1 : (term5 A B) = (@OUTL A B) => @lem1068518 A B h1)). Qed.
Lemma lem1068522 {A B : Type'} : (term5 A B) = (@OUTL A B).
Proof. exact (EQ_MP (@lem1068519 A B) (@lem1068509 A B)). Qed.
Lemma lem1068523 {A B : Type'} : (term5 A B) = (@OUTL A B).
Proof. exact (@lem1068522 A B). Qed.
Lemma lem1068524 {A B : Type'} (x : A) : (@inl A B x) = (@inl A B x).
Proof. exact (eq_refl (@inl A B x)). Qed.
Lemma lem1068525 {A B : Type'} (x : A) : (term6 A B x) = (term7 A B x).
Proof. exact (MK_COMB (@lem1068523 A B) (@lem1068524 A B x)). Qed.
Lemma lem1068526 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1068527 {A B : Type'} (x : A) : (term8 A B x) = (term9 A B x).
Proof. exact (MK_COMB (@lem1068526 A) (@lem1068525 A B x)). Qed.
Lemma lem1068528 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1068529 {A B : Type'} (x : A) : ((term6 A B x) = x) = ((term7 A B x) = x).
Proof. exact (MK_COMB (@lem1068527 A B x) (@lem1068528 A x)). Qed.
Lemma lem1068530 {A B : Type'} : (term10 A B) = (term11 A B).
Proof. exact (fun_ext (fun x : A => @lem1068529 A B x)). Qed.
Lemma lem1068531 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1068532 {A B : Type'} : (term4 A B) = (term12 A B).
Proof. exact (MK_COMB (@lem1068531 A) (@lem1068530 A B)). Qed.
Lemma lem1068533 {A B : Type'} : term12 A B.
Proof. exact (EQ_MP (@lem1068532 A B) (@lem1068514 A B)). Qed.
Lemma lem1068534 {A B : Type'} (x : A) : term13 A B x.
Proof. exact (@lem1068533 A B x). Qed.
Lemma lem1068535 {A B : Type'} (x : A) : (term13 A B x) = ((term7 A B x) = x).
Proof. exact (eq_refl (term13 A B x)). Qed.
Lemma lem1068536 {A B : Type'} (x : A) : (term7 A B x) = x.
Proof. exact (EQ_MP (@lem1068535 A B x) (@lem1068534 A B x)). Qed.
