Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_NOT_LT_term_abbrevs.
Require Import real_lt_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1376487 (y : real) : term0 y.
Proof. exact (@lem1341566 y). Qed.
Lemma lem1376488 (y : real) : (term0 y) = (term1 y).
Proof. exact (eq_refl (term0 y)). Qed.
Lemma lem1376489 (y : real) : term1 y.
Proof. exact (EQ_MP (@lem1376488 y) (@lem1376487 y)). Qed.
Lemma lem1376490 (y : real) (x : real) : term2 y x.
Proof. exact (@lem1376489 y x). Qed.
Lemma lem1376491 (y : real) (x : real) : (term2 y x) = ((real_lt x y) = (term3 y x)).
Proof. exact (eq_refl (term2 y x)). Qed.
Lemma lem1376504 (y : real) (x : real) : (real_lt x y) = (term3 y x).
Proof. exact (EQ_MP (@lem1376491 y x) (@lem1376490 y x)). Qed.
Lemma lem1376505 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1376506 (y : real) (x : real) : (term4 x y) = (term5 y x).
Proof. exact (MK_COMB (@lem1376505) (@lem1376504 y x)). Qed.
Lemma lem1376508 (t : Prop) : (term6 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem1376509 (y : real) (x : real) : (term5 y x) = (real_le y x).
Proof. exact (@lem1376508 (real_le y x)). Qed.
Lemma lem1376510 (y : real) (x : real) : (term4 x y) = (real_le y x).
Proof. exact (TRANS (@lem1376506 y x) (@lem1376509 y x)). Qed.
Lemma lem1376511 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1376512 (y : real) (x : real) : (term7 x y) = (term8 y x).
Proof. exact (MK_COMB (@lem1376511) (@lem1376510 y x)). Qed.
Lemma lem1376513 (y : real) (x : real) : (real_le y x) = (real_le y x).
Proof. exact (eq_refl (real_le y x)). Qed.
Lemma lem1376514 (y : real) (x : real) : ((term4 x y) = (real_le y x)) = ((real_le y x) = (real_le y x)).
Proof. exact (MK_COMB (@lem1376512 y x) (@lem1376513 y x)). Qed.
Lemma lem1376516 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1376517 (x : Prop) : (x = x) = True.
Proof. exact (@lem1376516 Prop x). Qed.
Lemma lem1376518 (y : real) (x : real) : ((real_le y x) = (real_le y x)) = True.
Proof. exact (@lem1376517 (real_le y x)). Qed.
Lemma lem1376519 (y : real) (x : real) : ((term4 x y) = (real_le y x)) = True.
Proof. exact (TRANS (@lem1376514 y x) (@lem1376518 y x)). Qed.
Lemma lem1376520 (x : real) : (term9 x) = term10.
Proof. exact (fun_ext (fun y : real => @lem1376519 y x)). Qed.
Lemma lem1376521 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1376522 (x : real) : (term11 x) = term12.
Proof. exact (MK_COMB (@lem1376521) (@lem1376520 x)). Qed.
Lemma lem1376524 {A : Type'} (t : Prop) : (term13 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1376525 (t : Prop) : (term14 t) = t.
Proof. exact (@lem1376524 real t). Qed.
Lemma lem1376526 : term12 = True.
Proof. exact (@lem1376525 True). Qed.
Lemma lem1376527 (x : real) : (term11 x) = True.
Proof. exact (TRANS (@lem1376522 x) (@lem1376526)). Qed.
Lemma lem1376528 : term15 = term10.
Proof. exact (fun_ext (fun x : real => @lem1376527 x)). Qed.
Lemma lem1376529 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1376530 : term16 = term12.
Proof. exact (MK_COMB (@lem1376529) (@lem1376528)). Qed.
Lemma lem1376532 {A : Type'} (t : Prop) : (term13 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1376533 (t : Prop) : (term14 t) = t.
Proof. exact (@lem1376532 real t). Qed.
Lemma lem1376534 : term12 = True.
Proof. exact (@lem1376533 True). Qed.
Lemma lem1376535 : term16 = True.
Proof. exact (TRANS (@lem1376530) (@lem1376534)). Qed.
Lemma lem1376536 : True = term16.
Proof. exact (SYM (@lem1376535)). Qed.
Lemma lem1376537 : term16.
Proof. exact (EQ_MP (@lem1376536) (@lem0)). Qed.
