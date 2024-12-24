Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1319496_term_abbrevs.
Require Import NADD_LE_TOTAL_spec.
Require Import thm1318142_spec.
Require Import thm1318147_spec.
Require Import thm1318759_spec.
Require Import thm1318760_spec.
Lemma lem1319419 (x : nadd) (y : nadd) : (nadd_le x y) = (term0 x y).
Proof. exact (EQ_MP (@lem1318147 x y) (@lem1318142 x y)). Qed.
Lemma lem1319420 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1319421 (x : nadd) (y : nadd) : (term1 x y) = (term2 x y).
Proof. exact (MK_COMB (@lem1319420) (@lem1319419 x y)). Qed.
Lemma lem1319423 (x : nadd) (y : nadd) : (nadd_le x y) = (term0 x y).
Proof. exact (EQ_MP (@lem1318147 x y) (@lem1318142 x y)). Qed.
Lemma lem1319424 (y : nadd) (x : nadd) : (nadd_le y x) = (term0 y x).
Proof. exact (@lem1319423 y x). Qed.
Lemma lem1319425 (y : nadd) (x : nadd) : (term3 y x) = (term4 y x).
Proof. exact (MK_COMB (@lem1319421 x y) (@lem1319424 y x)). Qed.
Lemma lem1319428 (x : nadd) : (term5 x) = (term6 x).
Proof. exact (fun_ext (fun y : nadd => @lem1319425 y x)). Qed.
Lemma lem1319429 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1319430 (x : nadd) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem1319429) (@lem1319428 x)). Qed.
Lemma lem1319436 (P : hreal -> Prop) : (term9 P) = (term10 P).
Proof. exact (EQ_MP (@lem1318760 P) (@lem1318759 P)). Qed.
Lemma lem1319437 (x : nadd) : (term11 x) = (term12 x).
Proof. exact (@lem1319436 (term13 x)). Qed.
Lemma lem1319438 (y : nadd) (x : nadd) : (term14 x y) = (term4 y x).
Proof. exact (eq_refl (term14 x y)). Qed.
Lemma lem1319439 (x : nadd) : (term15 x) = (term6 x).
Proof. exact (fun_ext (fun y : nadd => @lem1319438 y x)). Qed.
Lemma lem1319440 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1319441 (x : nadd) : (term11 x) = (term8 x).
Proof. exact (MK_COMB (@lem1319440) (@lem1319439 x)). Qed.
Lemma lem1319442 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1319443 (x : nadd) : (term16 x) = (term17 x).
Proof. exact (MK_COMB (@lem1319442) (@lem1319441 x)). Qed.
Lemma lem1319444 (y : hreal) (x : nadd) : (term18 x y) = (term19 y x).
Proof. exact (eq_refl (term18 x y)). Qed.
Lemma lem1319445 (x : nadd) : (term20 x) = (term13 x).
Proof. exact (fun_ext (fun y : hreal => @lem1319444 y x)). Qed.
Lemma lem1319446 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1319447 (x : nadd) : (term12 x) = (term21 x).
Proof. exact (MK_COMB (@lem1319446) (@lem1319445 x)). Qed.
Lemma lem1319448 (x : nadd) : ((term11 x) = (term12 x)) = ((term8 x) = (term21 x)).
Proof. exact (MK_COMB (@lem1319443 x) (@lem1319447 x)). Qed.
Lemma lem1319449 (x : nadd) : (term8 x) = (term21 x).
Proof. exact (EQ_MP (@lem1319448 x) (@lem1319437 x)). Qed.
Lemma lem1319458 (x : nadd) : (term7 x) = (term21 x).
Proof. exact (TRANS (@lem1319430 x) (@lem1319449 x)). Qed.
Lemma lem1319459 : term22 = term23.
Proof. exact (fun_ext (fun x : nadd => @lem1319458 x)). Qed.
Lemma lem1319460 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1319461 : term24 = term25.
Proof. exact (MK_COMB (@lem1319460) (@lem1319459)). Qed.
Lemma lem1319467 (P : hreal -> Prop) : (term9 P) = (term10 P).
Proof. exact (EQ_MP (@lem1318760 P) (@lem1318759 P)). Qed.
Lemma lem1319468 : term26 = term27.
Proof. exact (@lem1319467 term28). Qed.
Lemma lem1319469 (x : nadd) : (term29 x) = (term21 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1319470 : term30 = term23.
Proof. exact (fun_ext (fun x : nadd => @lem1319469 x)). Qed.
Lemma lem1319471 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1319472 : term26 = term25.
Proof. exact (MK_COMB (@lem1319471) (@lem1319470)). Qed.
Lemma lem1319473 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1319474 : term31 = term32.
Proof. exact (MK_COMB (@lem1319473) (@lem1319472)). Qed.
Lemma lem1319475 (x : hreal) : (term33 x) = (term34 x).
Proof. exact (eq_refl (term33 x)). Qed.
Lemma lem1319476 : term35 = term28.
Proof. exact (fun_ext (fun x : hreal => @lem1319475 x)). Qed.
Lemma lem1319477 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1319478 : term27 = term36.
Proof. exact (MK_COMB (@lem1319477) (@lem1319476)). Qed.
Lemma lem1319479 : (term26 = term27) = (term25 = term36).
Proof. exact (MK_COMB (@lem1319474) (@lem1319478)). Qed.
Lemma lem1319480 : term25 = term36.
Proof. exact (EQ_MP (@lem1319479) (@lem1319468)). Qed.
Lemma lem1319495 : term24 = term36.
Proof. exact (TRANS (@lem1319461) (@lem1319480)). Qed.
Lemma lem1319496 : term36.
Proof. exact (EQ_MP (@lem1319495) (@lem1273055)). Qed.
