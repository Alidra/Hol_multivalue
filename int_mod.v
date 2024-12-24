Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_mod_term_abbrevs.
Lemma lem2437325 : int_mod = term0.
Proof. exact (@int_mod_def). Qed.
Lemma lem2437326 (_29537 : int) : _29537 = _29537.
Proof. exact (eq_refl _29537). Qed.
Lemma lem2437327 (_29537 : int) : (int_mod _29537) = (term1 _29537).
Proof. exact (MK_COMB (@lem2437325) (@lem2437326 _29537)). Qed.
Lemma lem2437328 (_29537 : int) : (term1 _29537) = (term2 _29537).
Proof. exact (eq_refl (term1 _29537)). Qed.
Lemma lem2437329 (_29537 : int) : (int_mod _29537) = (term2 _29537).
Proof. exact (TRANS (@lem2437327 _29537) (@lem2437328 _29537)). Qed.
Lemma lem2437330 (_29538 : int) : _29538 = _29538.
Proof. exact (eq_refl _29538). Qed.
Lemma lem2437331 (_29537 : int) (_29538 : int) : (int_mod _29537 _29538) = (term3 _29537 _29538).
Proof. exact (MK_COMB (@lem2437329 _29537) (@lem2437330 _29538)). Qed.
Lemma lem2437332 (_29537 : int) (_29538 : int) : (term3 _29537 _29538) = (term4 _29537 _29538).
Proof. exact (eq_refl (term3 _29537 _29538)). Qed.
Lemma lem2437333 (_29537 : int) (_29538 : int) : (int_mod _29537 _29538) = (term4 _29537 _29538).
Proof. exact (TRANS (@lem2437331 _29537 _29538) (@lem2437332 _29537 _29538)). Qed.
Lemma lem2437334 (_29539 : int) : _29539 = _29539.
Proof. exact (eq_refl _29539). Qed.
Lemma lem2437335 (_29537 : int) (_29538 : int) (_29539 : int) : (int_mod _29537 _29538 _29539) = (term5 _29537 _29538 _29539).
Proof. exact (MK_COMB (@lem2437333 _29537 _29538) (@lem2437334 _29539)). Qed.
Lemma lem2437336 (_29537 : int) (_29538 : int) (_29539 : int) : (term5 _29537 _29538 _29539) = (term6 _29537 _29538 _29539).
Proof. exact (eq_refl (term5 _29537 _29538 _29539)). Qed.
Lemma lem2437337 (_29537 : int) (_29538 : int) (_29539 : int) : (int_mod _29537 _29538 _29539) = (term6 _29537 _29538 _29539).
Proof. exact (TRANS (@lem2437335 _29537 _29538 _29539) (@lem2437336 _29537 _29538 _29539)). Qed.
Lemma lem2437338 (_29537 : int) (_29538 : int) : term7 _29537 _29538.
Proof. exact (fun _29539 : int => @lem2437337 _29537 _29538 _29539). Qed.
Lemma lem2437339 (_29537 : int) : term8 _29537.
Proof. exact (fun _29538 : int => @lem2437338 _29537 _29538). Qed.
Lemma lem2437340 : term9.
Proof. exact (fun _29537 : int => @lem2437339 _29537). Qed.
Lemma lem2437341 (_29537 : int) : term10 _29537.
Proof. exact (@lem2437340 _29537). Qed.
Lemma lem2437342 (_29537 : int) : (term10 _29537) = (term8 _29537).
Proof. exact (eq_refl (term10 _29537)). Qed.
Lemma lem2437343 (_29537 : int) : term8 _29537.
Proof. exact (EQ_MP (@lem2437342 _29537) (@lem2437341 _29537)). Qed.
Lemma lem2437344 (_29537 : int) (_29538 : int) : term11 _29537 _29538.
Proof. exact (@lem2437343 _29537 _29538). Qed.
Lemma lem2437345 (_29537 : int) (_29538 : int) : (term11 _29537 _29538) = (term7 _29537 _29538).
Proof. exact (eq_refl (term11 _29537 _29538)). Qed.
Lemma lem2437346 (_29537 : int) (_29538 : int) : term7 _29537 _29538.
Proof. exact (EQ_MP (@lem2437345 _29537 _29538) (@lem2437344 _29537 _29538)). Qed.
Lemma lem2437347 (_29537 : int) (_29538 : int) (_29539 : int) : term12 _29537 _29538 _29539.
Proof. exact (@lem2437346 _29537 _29538 _29539). Qed.
Lemma lem2437348 (_29537 : int) (_29538 : int) (_29539 : int) : (term12 _29537 _29538 _29539) = ((int_mod _29537 _29538 _29539) = (term6 _29537 _29538 _29539)).
Proof. exact (eq_refl (term12 _29537 _29538 _29539)). Qed.
Lemma lem2437349 (_29537 : int) (_29538 : int) (_29539 : int) : (int_mod _29537 _29538 _29539) = (term6 _29537 _29538 _29539).
Proof. exact (EQ_MP (@lem2437348 _29537 _29538 _29539) (@lem2437347 _29537 _29538 _29539)). Qed.
Lemma lem2437405 (n : int) (x : int) (y : int) : (int_mod n x y) = (term6 n x y).
Proof. exact (@lem2437349 n x y). Qed.
Lemma lem2437406 (n : int) (x : int) : term7 n x.
Proof. exact (fun y : int => @lem2437405 n x y). Qed.
Lemma lem2437407 (n : int) : term8 n.
Proof. exact (fun x : int => @lem2437406 n x). Qed.
Lemma lem2437408 : term9.
Proof. exact (fun n : int => @lem2437407 n). Qed.
