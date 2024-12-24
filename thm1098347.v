Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1098347_term_abbrevs.
Require Import thm1097952_spec.
Require Import thm1098310_spec.
Lemma lem1098311 {A : Type'} : (term0 A) = (term1 A).
Proof. exact (eq_refl (term0 A)). Qed.
Lemma lem1098312 {A : Type'} : term1 A.
Proof. exact (EQ_MP (@lem1098311 A) (@lem1097952 A)). Qed.
Lemma lem1098313 {A : Type'} : term2 A.
Proof. exact (@lem1098312 A term3). Qed.
Lemma lem1098314 {A : Type'} : (term2 A) = (term4 A).
Proof. exact (eq_refl (term2 A)). Qed.
Lemma lem1098315 {A : Type'} : term4 A.
Proof. exact (EQ_MP (@lem1098314 A) (@lem1098313 A)). Qed.
Lemma lem1098316 {A : Type'} (h1 : (@LAST A) = (term5 A)) : (@LAST A) = (term5 A).
Proof. exact (h1). Qed.
Lemma lem1098317 {A : Type'} (h1 : (@LAST A) = (term5 A)) : (term5 A) = (@LAST A).
Proof. exact (SYM (@lem1098316 A h1)). Qed.
Lemma lem1098318 {A : Type'} (h1 : (term5 A) = (@LAST A)) : (term5 A) = (@LAST A).
Proof. exact (h1). Qed.
Lemma lem1098319 {A : Type'} (h1 : (term5 A) = (@LAST A)) : (@LAST A) = (term5 A).
Proof. exact (SYM (@lem1098318 A h1)). Qed.
Lemma lem1098320 {A : Type'} : ((@LAST A) = (term5 A)) = ((term5 A) = (@LAST A)).
Proof. exact (prop_ext (fun h1 : (@LAST A) = (term5 A) => @lem1098317 A h1) (fun h1 : (term5 A) = (@LAST A) => @lem1098319 A h1)). Qed.
Lemma lem1098323 {A : Type'} : (term5 A) = (@LAST A).
Proof. exact (EQ_MP (@lem1098320 A) (@lem1098310 A)). Qed.
Lemma lem1098324 {A : Type'} : (term5 A) = (@LAST A).
Proof. exact (@lem1098323 A). Qed.
Lemma lem1098325 {A : Type'} (h : A) (t : list A) : (@cons A h t) = (@cons A h t).
Proof. exact (eq_refl (@cons A h t)). Qed.
Lemma lem1098326 {A : Type'} (h : A) (t : list A) : (term6 A h t) = (term7 A h t).
Proof. exact (MK_COMB (@lem1098324 A) (@lem1098325 A h t)). Qed.
Lemma lem1098327 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1098328 {A : Type'} (h : A) (t : list A) : (term8 A h t) = (term9 A h t).
Proof. exact (MK_COMB (@lem1098327 A) (@lem1098326 A h t)). Qed.
Lemma lem1098330 {A : Type'} : (term5 A) = (@LAST A).
Proof. exact (EQ_MP (@lem1098320 A) (@lem1098310 A)). Qed.
Lemma lem1098331 {A : Type'} : (term5 A) = (@LAST A).
Proof. exact (@lem1098330 A). Qed.
Lemma lem1098332 {A : Type'} (t : list A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1098333 {A : Type'} (t : list A) : (term10 A t) = (@LAST A t).
Proof. exact (MK_COMB (@lem1098331 A) (@lem1098332 A t)). Qed.
Lemma lem1098334 {A : Type'} (t : list A) (h : A) : (term11 A t h) = (term11 A t h).
Proof. exact (eq_refl (term11 A t h)). Qed.
Lemma lem1098335 {A : Type'} (h : A) (t : list A) : (term12 A h t) = (term13 A h t).
Proof. exact (MK_COMB (@lem1098334 A t h) (@lem1098333 A t)). Qed.
Lemma lem1098336 {A : Type'} (h : A) (t : list A) : ((term6 A h t) = (term12 A h t)) = ((term7 A h t) = (term13 A h t)).
Proof. exact (MK_COMB (@lem1098328 A h t) (@lem1098335 A h t)). Qed.
Lemma lem1098337 {A : Type'} (h : A) : (term14 A h) = (term15 A h).
Proof. exact (fun_ext (fun t : list A => @lem1098336 A h t)). Qed.
Lemma lem1098338 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1098339 {A : Type'} (h : A) : (term16 A h) = (term17 A h).
Proof. exact (MK_COMB (@lem1098338 A) (@lem1098337 A h)). Qed.
Lemma lem1098340 {A : Type'} : (term18 A) = (term19 A).
Proof. exact (fun_ext (fun h : A => @lem1098339 A h)). Qed.
Lemma lem1098341 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1098342 {A : Type'} : (term4 A) = (term20 A).
Proof. exact (MK_COMB (@lem1098341 A) (@lem1098340 A)). Qed.
Lemma lem1098343 {A : Type'} : term20 A.
Proof. exact (EQ_MP (@lem1098342 A) (@lem1098315 A)). Qed.
Lemma lem1098344 {A : Type'} (h : A) : term21 A h.
Proof. exact (@lem1098343 A h). Qed.
Lemma lem1098345 {A : Type'} (h : A) : (term21 A h) = (term17 A h).
Proof. exact (eq_refl (term21 A h)). Qed.
Lemma lem1098346 {A : Type'} (h : A) : term17 A h.
Proof. exact (EQ_MP (@lem1098345 A h) (@lem1098344 A h)). Qed.
Lemma lem1098347 {A : Type'} (h : A) (t : list A) : term22 A h t.
Proof. exact (@lem1098346 A h t). Qed.
