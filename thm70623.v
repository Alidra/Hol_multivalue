Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm70623_term_abbrevs.
Require Import IND_SUC_0_EXISTS_spec.
Require Import thm70521_spec.
Require Import thm9396_spec.
Lemma lem70522 (P : type922) : term0 P.
Proof. exact (@lem9396 (ind -> ind) P). Qed.
Lemma lem70523 : term1.
Proof. exact (@lem70522 term2). Qed.
Lemma lem70524 : term3.
Proof. exact (@lem70523 (@lem70373)). Qed.
Lemma lem70525 : term3 = term4.
Proof. exact (eq_refl term3). Qed.
Lemma lem70526 : term4.
Proof. exact (EQ_MP (@lem70525) (@lem70524)). Qed.
Lemma lem70527 (h1 : IND_SUC = term5) : IND_SUC = term5.
Proof. exact (h1). Qed.
Lemma lem70528 (h1 : IND_SUC = term5) : term5 = IND_SUC.
Proof. exact (SYM (@lem70527 h1)). Qed.
Lemma lem70529 (h1 : term5 = IND_SUC) : term5 = IND_SUC.
Proof. exact (h1). Qed.
Lemma lem70530 (h1 : term5 = IND_SUC) : IND_SUC = term5.
Proof. exact (SYM (@lem70529 h1)). Qed.
Lemma lem70531 : (IND_SUC = term5) = (term5 = IND_SUC).
Proof. exact (prop_ext (fun h1 : IND_SUC = term5 => @lem70528 h1) (fun h1 : term5 = IND_SUC => @lem70530 h1)). Qed.
Lemma lem70552 : term5 = IND_SUC.
Proof. exact (EQ_MP (@lem70531) (@lem70521)). Qed.
Lemma lem70553 (x1 : ind) : x1 = x1.
Proof. exact (eq_refl x1). Qed.
Lemma lem70554 (x1 : ind) : (term6 x1) = (IND_SUC x1).
Proof. exact (MK_COMB (@lem70552) (@lem70553 x1)). Qed.
Lemma lem70555 : (@eq ind) = (@eq ind).
Proof. exact (eq_refl (@eq ind)). Qed.
Lemma lem70556 (x1 : ind) : (term7 x1) = (term8 x1).
Proof. exact (MK_COMB (@lem70555) (@lem70554 x1)). Qed.
Lemma lem70558 : term5 = IND_SUC.
Proof. exact (EQ_MP (@lem70531) (@lem70521)). Qed.
Lemma lem70559 (x2 : ind) : x2 = x2.
Proof. exact (eq_refl x2). Qed.
Lemma lem70560 (x2 : ind) : (term6 x2) = (IND_SUC x2).
Proof. exact (MK_COMB (@lem70558) (@lem70559 x2)). Qed.
Lemma lem70561 (x1 : ind) (x2 : ind) : ((term6 x1) = (term6 x2)) = ((IND_SUC x1) = (IND_SUC x2)).
Proof. exact (MK_COMB (@lem70556 x1) (@lem70560 x2)). Qed.
Lemma lem70564 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem70565 (x1 : ind) (x2 : ind) : (term9 x1 x2) = (term10 x1 x2).
Proof. exact (MK_COMB (@lem70564) (@lem70561 x1 x2)). Qed.
Lemma lem70568 (x1 : ind) (x2 : ind) : (x1 = x2) = (x1 = x2).
Proof. exact (eq_refl (x1 = x2)). Qed.
Lemma lem70569 (x1 : ind) (x2 : ind) : (((term6 x1) = (term6 x2)) = (x1 = x2)) = (((IND_SUC x1) = (IND_SUC x2)) = (x1 = x2)).
Proof. exact (MK_COMB (@lem70565 x1 x2) (@lem70568 x1 x2)). Qed.
Lemma lem70572 (x1 : ind) : (term11 x1) = (term12 x1).
Proof. exact (fun_ext (fun x2 : ind => @lem70569 x1 x2)). Qed.
Lemma lem70573 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem70574 (x1 : ind) : (term13 x1) = (term14 x1).
Proof. exact (MK_COMB (@lem70573) (@lem70572 x1)). Qed.
Lemma lem70579 : term15 = term16.
Proof. exact (fun_ext (fun x1 : ind => @lem70574 x1)). Qed.
Lemma lem70580 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem70581 : term17 = term18.
Proof. exact (MK_COMB (@lem70580) (@lem70579)). Qed.
Lemma lem70586 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem70587 : term19 = term20.
Proof. exact (MK_COMB (@lem70586) (@lem70581)). Qed.
Lemma lem70595 : term5 = IND_SUC.
Proof. exact (EQ_MP (@lem70531) (@lem70521)). Qed.
Lemma lem70596 (x : ind) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem70597 (x : ind) : (term6 x) = (IND_SUC x).
Proof. exact (MK_COMB (@lem70595) (@lem70596 x)). Qed.
Lemma lem70598 : (@eq ind) = (@eq ind).
Proof. exact (eq_refl (@eq ind)). Qed.
Lemma lem70599 (x : ind) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem70598) (@lem70597 x)). Qed.
Lemma lem70600 (z : ind) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem70601 (x : ind) (z : ind) : ((term6 x) = z) = ((IND_SUC x) = z).
Proof. exact (MK_COMB (@lem70599 x) (@lem70600 z)). Qed.
Lemma lem70604 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem70605 (x : ind) (z : ind) : (term21 x z) = (term22 x z).
Proof. exact (MK_COMB (@lem70604) (@lem70601 x z)). Qed.
Lemma lem70606 (z : ind) : (term23 z) = (term24 z).
Proof. exact (fun_ext (fun x : ind => @lem70605 x z)). Qed.
Lemma lem70607 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem70608 (z : ind) : (term25 z) = (term26 z).
Proof. exact (MK_COMB (@lem70607) (@lem70606 z)). Qed.
Lemma lem70613 (z : ind) : (term27 z) = (term28 z).
Proof. exact (MK_COMB (@lem70587) (@lem70608 z)). Qed.
Lemma lem70616 : term29 = term30.
Proof. exact (fun_ext (fun z : ind => @lem70613 z)). Qed.
Lemma lem70617 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem70618 : term4 = term31.
Proof. exact (MK_COMB (@lem70617) (@lem70616)). Qed.
Lemma lem70623 : term31.
Proof. exact (EQ_MP (@lem70618) (@lem70526)). Qed.
