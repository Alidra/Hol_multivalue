Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1339240_term_abbrevs.
Require Import TREAL_LE_REFL_spec.
Require Import thm1337985_spec.
Require Import thm1337990_spec.
Require Import thm1338105_spec.
Require Import thm1338106_spec.
Lemma lem1339209 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (treal_le x1 y1) = (term0 x1 y1).
Proof. exact (EQ_MP (@lem1337990 x1 y1) (@lem1337985 x1 y1)). Qed.
Lemma lem1339210 (x : prod hreal hreal) : (treal_le x x) = (term1 x).
Proof. exact (@lem1339209 x x). Qed.
Lemma lem1339211 : term2 = term3.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1339210 x)). Qed.
Lemma lem1339212 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339213 : term4 = term5.
Proof. exact (MK_COMB (@lem1339212) (@lem1339211)). Qed.
Lemma lem1339219 (P : real -> Prop) : (term6 P) = (term7 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1339220 : term8 = term9.
Proof. exact (@lem1339219 term10). Qed.
Lemma lem1339221 (x : prod hreal hreal) : (term11 x) = (term1 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1339222 : term12 = term3.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1339221 x)). Qed.
Lemma lem1339223 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339224 : term8 = term5.
Proof. exact (MK_COMB (@lem1339223) (@lem1339222)). Qed.
Lemma lem1339225 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1339226 : term13 = term14.
Proof. exact (MK_COMB (@lem1339225) (@lem1339224)). Qed.
Lemma lem1339227 (x : real) : (term15 x) = (real_le x x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1339228 : term16 = term10.
Proof. exact (fun_ext (fun x : real => @lem1339227 x)). Qed.
Lemma lem1339229 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1339230 : term9 = term17.
Proof. exact (MK_COMB (@lem1339229) (@lem1339228)). Qed.
Lemma lem1339231 : (term8 = term9) = (term5 = term17).
Proof. exact (MK_COMB (@lem1339226) (@lem1339230)). Qed.
Lemma lem1339232 : term5 = term17.
Proof. exact (EQ_MP (@lem1339231) (@lem1339220)). Qed.
Lemma lem1339239 : term4 = term17.
Proof. exact (TRANS (@lem1339213) (@lem1339232)). Qed.
Lemma lem1339240 : term17.
Proof. exact (EQ_MP (@lem1339239) (@lem1329971)). Qed.
