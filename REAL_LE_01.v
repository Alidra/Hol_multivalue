Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_01_term_abbrevs.
Require Import thm1008952_spec.
Require Import thm1366270_spec.
Require Import thm1367247_spec.
Require Import thm1386578_spec.
Require Import thm1483448_spec.
Require Import thm1483519_spec.
Require Import thm1483533_spec.
Require Import thm940073_spec.
Lemma lem1499267 : term0 = term1.
Proof. exact (@lem1483533 term2 term3). Qed.
Lemma lem1499273 : term4 = term5.
Proof. exact (@lem1483519 term2 term3). Qed.
Lemma lem1499275 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1499276 : term8 = term9.
Proof. exact (@lem1499275 term10 term10). Qed.
Lemma lem1499277 : (term11 = (BIT1 0)) = (term12 = term10).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1499278 : term12 = term10.
Proof. exact (EQ_MP (@lem1499277) (@lem940073)). Qed.
Lemma lem1499279 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1499280 : term13 = term3.
Proof. exact (MK_COMB (@lem1499279) (@lem1499278)). Qed.
Lemma lem1499281 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1499282 : term9 = term14.
Proof. exact (MK_COMB (@lem1499281) (@lem1499280)). Qed.
Lemma lem1499283 : term8 = term14.
Proof. exact (TRANS (@lem1499276) (@lem1499282)). Qed.
Lemma lem1499284 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1499285 : term5 = term16.
Proof. exact (MK_COMB (@lem1499284) (@lem1499283)). Qed.
Lemma lem1499286 : term16 = term14.
Proof. exact (@lem1483448 term14). Qed.
Lemma lem1499287 : term5 = term14.
Proof. exact (TRANS (@lem1499285) (@lem1499286)). Qed.
Lemma lem1499289 : term4 = term14.
Proof. exact (TRANS (@lem1499273) (@lem1499287)). Qed.
Lemma lem1499290 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1499291 : term17 = term18.
Proof. exact (MK_COMB (@lem1499290) (@lem1499289)). Qed.
Lemma lem1499292 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1499293 : term1 = term19.
Proof. exact (MK_COMB (@lem1499291) (@lem1499292)). Qed.
Lemma lem1499303 : term0 = term19.
Proof. exact (TRANS (@lem1499267) (@lem1499293)). Qed.
Lemma lem1499307 (h1 : term19) : term19.
Proof. exact (h1). Qed.
Lemma lem1499309 (m : nat) (n : nat) : (term20 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1499310 : term19 = False.
Proof. exact (@lem1499309 term10 (NUMERAL 0)). Qed.
Lemma lem1499311 (h1 : term19) : False.
Proof. exact (EQ_MP (@lem1499310) (@lem1499307 h1)). Qed.
Lemma lem1499313 (h1 : term19) : term19.
Proof. exact (h1). Qed.
Lemma lem1499314 (h1 : term19) : term19 = False.
Proof. exact (prop_ext (fun h2 : term19 => @lem1499311 h1) (fun h2 : False => @lem1499313 h1)). Qed.
Lemma lem1499315 (h1 : term19) : False.
Proof. exact (EQ_MP (@lem1499314 h1) (@lem1499313 h1)). Qed.
Lemma lem1499316 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1499317 (h1 : term0) : term19.
Proof. exact (EQ_MP (@lem1499303) (@lem1499316 h1)). Qed.
Lemma lem1499318 (h1 : term0) : term19 = False.
Proof. exact (prop_ext (fun h2 : term19 => @lem1499315 h2) (fun h2 : False => @lem1499317 h1)). Qed.
Lemma lem1499319 (h1 : term0) : False.
Proof. exact (EQ_MP (@lem1499318 h1) (@lem1499317 h1)). Qed.
Lemma lem1499320 : term21.
Proof. exact (fun h0 : term0 => @lem1499319 h0). Qed.
Lemma lem1499321 : term22.
Proof. exact (@lem1386578 term23). Qed.
Lemma lem1499322 : term23.
Proof. exact (@lem1499321 (@lem1499320)). Qed.
