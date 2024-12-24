Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1319607_term_abbrevs.
Require Import NADD_LE_ADD_spec.
Require Import thm1317906_spec.
Require Import thm1317911_spec.
Require Import thm1318142_spec.
Require Import thm1318147_spec.
Require Import thm1318759_spec.
Require Import thm1318760_spec.
Lemma lem1319536 (x : nadd) (y : nadd) : (nadd_le x y) = (term0 x y).
Proof. exact (EQ_MP (@lem1318147 x y) (@lem1318142 x y)). Qed.
Lemma lem1319537 (x : nadd) (y : nadd) : (term1 x y) = (term2 x y).
Proof. exact (@lem1319536 x (nadd_add x y)). Qed.
Lemma lem1319539 (x : nadd) (y : nadd) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem1317911 x y) (@lem1317906 x y)). Qed.
Lemma lem1319540 (x : nadd) : (term5 x) = (term5 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1319541 (x : nadd) (y : nadd) : (term2 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem1319540 x) (@lem1319539 x y)). Qed.
Lemma lem1319542 (x : nadd) (y : nadd) : (term1 x y) = (term6 x y).
Proof. exact (TRANS (@lem1319537 x y) (@lem1319541 x y)). Qed.
Lemma lem1319543 (x : nadd) : (term7 x) = (term8 x).
Proof. exact (fun_ext (fun y : nadd => @lem1319542 x y)). Qed.
Lemma lem1319544 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1319545 (x : nadd) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem1319544) (@lem1319543 x)). Qed.
Lemma lem1319551 (P : hreal -> Prop) : (term11 P) = (term12 P).
Proof. exact (EQ_MP (@lem1318760 P) (@lem1318759 P)). Qed.
Lemma lem1319552 (x : nadd) : (term13 x) = (term14 x).
Proof. exact (@lem1319551 (term15 x)). Qed.
Lemma lem1319553 (x : nadd) (y : nadd) : (term16 x y) = (term6 x y).
Proof. exact (eq_refl (term16 x y)). Qed.
Lemma lem1319554 (x : nadd) : (term17 x) = (term8 x).
Proof. exact (fun_ext (fun y : nadd => @lem1319553 x y)). Qed.
Lemma lem1319555 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1319556 (x : nadd) : (term13 x) = (term10 x).
Proof. exact (MK_COMB (@lem1319555) (@lem1319554 x)). Qed.
Lemma lem1319557 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1319558 (x : nadd) : (term18 x) = (term19 x).
Proof. exact (MK_COMB (@lem1319557) (@lem1319556 x)). Qed.
Lemma lem1319559 (x : nadd) (y : hreal) : (term20 x y) = (term21 x y).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem1319560 (x : nadd) : (term22 x) = (term15 x).
Proof. exact (fun_ext (fun y : hreal => @lem1319559 x y)). Qed.
Lemma lem1319561 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1319562 (x : nadd) : (term14 x) = (term23 x).
Proof. exact (MK_COMB (@lem1319561) (@lem1319560 x)). Qed.
Lemma lem1319563 (x : nadd) : ((term13 x) = (term14 x)) = ((term10 x) = (term23 x)).
Proof. exact (MK_COMB (@lem1319558 x) (@lem1319562 x)). Qed.
Lemma lem1319564 (x : nadd) : (term10 x) = (term23 x).
Proof. exact (EQ_MP (@lem1319563 x) (@lem1319552 x)). Qed.
Lemma lem1319571 (x : nadd) : (term9 x) = (term23 x).
Proof. exact (TRANS (@lem1319545 x) (@lem1319564 x)). Qed.
Lemma lem1319572 : term24 = term25.
Proof. exact (fun_ext (fun x : nadd => @lem1319571 x)). Qed.
Lemma lem1319573 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1319574 : term26 = term27.
Proof. exact (MK_COMB (@lem1319573) (@lem1319572)). Qed.
Lemma lem1319580 (P : hreal -> Prop) : (term11 P) = (term12 P).
Proof. exact (EQ_MP (@lem1318760 P) (@lem1318759 P)). Qed.
Lemma lem1319581 : term28 = term29.
Proof. exact (@lem1319580 term30). Qed.
Lemma lem1319582 (x : nadd) : (term31 x) = (term23 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem1319583 : term32 = term25.
Proof. exact (fun_ext (fun x : nadd => @lem1319582 x)). Qed.
Lemma lem1319584 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1319585 : term28 = term27.
Proof. exact (MK_COMB (@lem1319584) (@lem1319583)). Qed.
Lemma lem1319586 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1319587 : term33 = term34.
Proof. exact (MK_COMB (@lem1319586) (@lem1319585)). Qed.
Lemma lem1319588 (x : hreal) : (term35 x) = (term36 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem1319589 : term37 = term30.
Proof. exact (fun_ext (fun x : hreal => @lem1319588 x)). Qed.
Lemma lem1319590 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1319591 : term29 = term38.
Proof. exact (MK_COMB (@lem1319590) (@lem1319589)). Qed.
Lemma lem1319592 : (term28 = term29) = (term27 = term38).
Proof. exact (MK_COMB (@lem1319587) (@lem1319591)). Qed.
Lemma lem1319593 : term27 = term38.
Proof. exact (EQ_MP (@lem1319592) (@lem1319581)). Qed.
Lemma lem1319606 : term26 = term38.
Proof. exact (TRANS (@lem1319574) (@lem1319593)). Qed.
Lemma lem1319607 : term38.
Proof. exact (EQ_MP (@lem1319606) (@lem1275082)). Qed.
