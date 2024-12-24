Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1095388_term_abbrevs.
Require Import thm1095009_spec.
Require Import thm1095357_spec.
Lemma lem1095358 {A : Type'} : (term0 A) = (term1 A).
Proof. exact (eq_refl (term0 A)). Qed.
Lemma lem1095359 {A : Type'} : term1 A.
Proof. exact (EQ_MP (@lem1095358 A) (@lem1095009 A)). Qed.
Lemma lem1095360 {A : Type'} : term2 A.
Proof. exact (@lem1095359 A term3). Qed.
Lemma lem1095361 {A : Type'} : (term2 A) = (term4 A).
Proof. exact (eq_refl (term2 A)). Qed.
Lemma lem1095362 {A : Type'} : term4 A.
Proof. exact (EQ_MP (@lem1095361 A) (@lem1095360 A)). Qed.
Lemma lem1095363 {A : Type'} (h1 : (@tl A) = (term5 A)) : (@tl A) = (term5 A).
Proof. exact (h1). Qed.
Lemma lem1095364 {A : Type'} (h1 : (@tl A) = (term5 A)) : (term5 A) = (@tl A).
Proof. exact (SYM (@lem1095363 A h1)). Qed.
Lemma lem1095365 {A : Type'} (h1 : (term5 A) = (@tl A)) : (term5 A) = (@tl A).
Proof. exact (h1). Qed.
Lemma lem1095366 {A : Type'} (h1 : (term5 A) = (@tl A)) : (@tl A) = (term5 A).
Proof. exact (SYM (@lem1095365 A h1)). Qed.
Lemma lem1095367 {A : Type'} : ((@tl A) = (term5 A)) = ((term5 A) = (@tl A)).
Proof. exact (prop_ext (fun h1 : (@tl A) = (term5 A) => @lem1095364 A h1) (fun h1 : (term5 A) = (@tl A) => @lem1095366 A h1)). Qed.
Lemma lem1095370 {A : Type'} : (term5 A) = (@tl A).
Proof. exact (EQ_MP (@lem1095367 A) (@lem1095357 A)). Qed.
Lemma lem1095371 {A : Type'} : (term5 A) = (@tl A).
Proof. exact (@lem1095370 A). Qed.
Lemma lem1095372 {A : Type'} (h : A) (t : list A) : (@cons A h t) = (@cons A h t).
Proof. exact (eq_refl (@cons A h t)). Qed.
Lemma lem1095373 {A : Type'} (h : A) (t : list A) : (term6 A h t) = (term7 A h t).
Proof. exact (MK_COMB (@lem1095371 A) (@lem1095372 A h t)). Qed.
Lemma lem1095374 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1095375 {A : Type'} (h : A) (t : list A) : (term8 A h t) = (term9 A h t).
Proof. exact (MK_COMB (@lem1095374 A) (@lem1095373 A h t)). Qed.
Lemma lem1095376 {A : Type'} (t : list A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1095377 {A : Type'} (h : A) (t : list A) : ((term6 A h t) = t) = ((term7 A h t) = t).
Proof. exact (MK_COMB (@lem1095375 A h t) (@lem1095376 A t)). Qed.
Lemma lem1095378 {A : Type'} (h : A) : (term10 A h) = (term11 A h).
Proof. exact (fun_ext (fun t : list A => @lem1095377 A h t)). Qed.
Lemma lem1095379 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1095380 {A : Type'} (h : A) : (term12 A h) = (term13 A h).
Proof. exact (MK_COMB (@lem1095379 A) (@lem1095378 A h)). Qed.
Lemma lem1095381 {A : Type'} : (term14 A) = (term15 A).
Proof. exact (fun_ext (fun h : A => @lem1095380 A h)). Qed.
Lemma lem1095382 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1095383 {A : Type'} : (term4 A) = (term16 A).
Proof. exact (MK_COMB (@lem1095382 A) (@lem1095381 A)). Qed.
Lemma lem1095384 {A : Type'} : term16 A.
Proof. exact (EQ_MP (@lem1095383 A) (@lem1095362 A)). Qed.
Lemma lem1095385 {A : Type'} (h : A) : term17 A h.
Proof. exact (@lem1095384 A h). Qed.
Lemma lem1095386 {A : Type'} (h : A) : (term17 A h) = (term13 A h).
Proof. exact (eq_refl (term17 A h)). Qed.
Lemma lem1095387 {A : Type'} (h : A) : term13 A h.
Proof. exact (EQ_MP (@lem1095386 A h) (@lem1095385 A h)). Qed.
Lemma lem1095388 {A : Type'} (h : A) (t : list A) : term18 A h t.
Proof. exact (@lem1095387 A h t). Qed.
