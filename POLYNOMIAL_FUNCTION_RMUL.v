Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import POLYNOMIAL_FUNCTION_RMUL_term_abbrevs.
Require Import POLYNOMIAL_FUNCTION_LMUL_spec.
Require Import thm0_spec.
Require Import thm1338712_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem7567526 (p : real -> real) : term0 p.
Proof. exact (@lem7567525 p). Qed.
Lemma lem7567527 (p : real -> real) : (term0 p) = (term1 p).
Proof. exact (eq_refl (term0 p)). Qed.
Lemma lem7567528 (p : real -> real) : term1 p.
Proof. exact (EQ_MP (@lem7567527 p) (@lem7567526 p)). Qed.
Lemma lem7567529 (p : real -> real) (c : real) : term2 p c.
Proof. exact (@lem7567528 p c). Qed.
Lemma lem7567530 (c : real) (p : real -> real) : (term2 p c) = (term3 c p).
Proof. exact (eq_refl (term2 p c)). Qed.
Lemma lem7567531 (c : real) (p : real -> real) : term3 c p.
Proof. exact (EQ_MP (@lem7567530 c p) (@lem7567529 p c)). Qed.
Lemma lem7567532 (c : real) (p : real -> real) : (term3 c p) = ((term3 c p) = True).
Proof. exact (@lem7 (term3 c p)). Qed.
Lemma lem7567534 (x : real) : term4 x.
Proof. exact (@lem1338712 x). Qed.
Lemma lem7567535 (x : real) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem7567536 (x : real) : term5 x.
Proof. exact (EQ_MP (@lem7567535 x) (@lem7567534 x)). Qed.
Lemma lem7567537 (x : real) (y : real) : term6 x y.
Proof. exact (@lem7567536 x y). Qed.
Lemma lem7567538 (y : real) (x : real) : (term6 x y) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem7567551 (y : real) (x : real) : (real_mul x y) = (real_mul y x).
Proof. exact (EQ_MP (@lem7567538 y x) (@lem7567537 x y)). Qed.
Lemma lem7567552 (c : real) (p : real -> real) (x : real) : (term7 p x c) = (term8 c p x).
Proof. exact (@lem7567551 c (p x)). Qed.
Lemma lem7567553 (c : real) (p : real -> real) : (term9 p c) = (term10 c p).
Proof. exact (fun_ext (fun x : real => @lem7567552 c p x)). Qed.
Lemma lem7567554 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7567555 (c : real) (p : real -> real) : (term11 p c) = (term12 c p).
Proof. exact (MK_COMB (@lem7567554) (@lem7567553 c p)). Qed.
Lemma lem7567556 (p : real -> real) : (term13 p) = (term13 p).
Proof. exact (eq_refl (term13 p)). Qed.
Lemma lem7567557 (c : real) (p : real -> real) : (term14 p c) = (term3 c p).
Proof. exact (MK_COMB (@lem7567556 p) (@lem7567555 c p)). Qed.
Lemma lem7567558 (p : real -> real) : (term15 p) = (term16 p).
Proof. exact (fun_ext (fun c : real => @lem7567557 c p)). Qed.
Lemma lem7567559 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7567560 (p : real -> real) : (term17 p) = (term1 p).
Proof. exact (MK_COMB (@lem7567559) (@lem7567558 p)). Qed.
Lemma lem7567561 : term18 = term19.
Proof. exact (fun_ext (fun p : real -> real => @lem7567560 p)). Qed.
Lemma lem7567562 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7567563 : term20 = term21.
Proof. exact (MK_COMB (@lem7567562) (@lem7567561)). Qed.
Lemma lem7567564 : term21 = term20.
Proof. exact (SYM (@lem7567563)). Qed.
Lemma lem7567574 (c : real) (p : real -> real) : (term3 c p) = True.
Proof. exact (EQ_MP (@lem7567532 c p) (@lem7567531 c p)). Qed.
Lemma lem7567575 (p : real -> real) : (term16 p) = term22.
Proof. exact (fun_ext (fun c : real => @lem7567574 c p)). Qed.
Lemma lem7567576 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7567577 (p : real -> real) : (term1 p) = term23.
Proof. exact (MK_COMB (@lem7567576) (@lem7567575 p)). Qed.
Lemma lem7567579 {A : Type'} (t : Prop) : (term24 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7567580 (t : Prop) : (term25 t) = t.
Proof. exact (@lem7567579 real t). Qed.
Lemma lem7567581 : term23 = True.
Proof. exact (@lem7567580 True). Qed.
Lemma lem7567582 (p : real -> real) : (term1 p) = True.
Proof. exact (TRANS (@lem7567577 p) (@lem7567581)). Qed.
Lemma lem7567583 : term19 = term26.
Proof. exact (fun_ext (fun p : real -> real => @lem7567582 p)). Qed.
Lemma lem7567584 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7567585 : term21 = term27.
Proof. exact (MK_COMB (@lem7567584) (@lem7567583)). Qed.
Lemma lem7567587 {A : Type'} (t : Prop) : (term24 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7567588 (t : Prop) : (term28 t) = t.
Proof. exact (@lem7567587 (real -> real) t). Qed.
Lemma lem7567589 : term27 = True.
Proof. exact (@lem7567588 True). Qed.
Lemma lem7567590 : term21 = True.
Proof. exact (TRANS (@lem7567585) (@lem7567589)). Qed.
Lemma lem7567591 : True = term21.
Proof. exact (SYM (@lem7567590)). Qed.
Lemma lem7567592 : term21.
Proof. exact (EQ_MP (@lem7567591) (@lem0)). Qed.
Lemma lem7567593 : term20.
Proof. exact (EQ_MP (@lem7567564) (@lem7567592)). Qed.
