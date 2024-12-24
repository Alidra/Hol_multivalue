Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import tailadmissible_term_abbrevs.
Lemma lem8094539 {A B P : Type'} : (@tailadmissible A B P) = (term0 A B P).
Proof. exact (@tailadmissible_def A B P). Qed.
Lemma lem8094540 {A : Type'} (_107321 : type1402 A) : _107321 = _107321.
Proof. exact (eq_refl _107321). Qed.
Lemma lem8094541 {A B P : Type'} (_107321 : type1402 A) : (@tailadmissible A B P _107321) = (term1 A B P _107321).
Proof. exact (MK_COMB (@lem8094539 A B P) (@lem8094540 A _107321)). Qed.
Lemma lem8094542 {A B P : Type'} (_107321 : type1402 A) : (term1 A B P _107321) = (term2 A B P _107321).
Proof. exact (eq_refl (term1 A B P _107321)). Qed.
Lemma lem8094543 {A B P : Type'} (_107321 : type1402 A) : (@tailadmissible A B P _107321) = (term2 A B P _107321).
Proof. exact (TRANS (@lem8094541 A B P _107321) (@lem8094542 A B P _107321)). Qed.
Lemma lem8094544 {A B P : Type'} (_107322 : type560 A B P) : _107322 = _107322.
Proof. exact (eq_refl _107322). Qed.
Lemma lem8094545 {A B P : Type'} (_107321 : type1402 A) (_107322 : type560 A B P) : (@tailadmissible A B P _107321 _107322) = (term3 A B P _107321 _107322).
Proof. exact (MK_COMB (@lem8094543 A B P _107321) (@lem8094544 A B P _107322)). Qed.
Lemma lem8094546 {A B P : Type'} (_107321 : type1402 A) (_107322 : type560 A B P) : (term3 A B P _107321 _107322) = (term4 A B P _107321 _107322).
Proof. exact (eq_refl (term3 A B P _107321 _107322)). Qed.
Lemma lem8094547 {A B P : Type'} (_107321 : type1402 A) (_107322 : type560 A B P) : (@tailadmissible A B P _107321 _107322) = (term4 A B P _107321 _107322).
Proof. exact (TRANS (@lem8094545 A B P _107321 _107322) (@lem8094546 A B P _107321 _107322)). Qed.
Lemma lem8094548 {A P : Type'} (_107323 : P -> A) : _107323 = _107323.
Proof. exact (eq_refl _107323). Qed.
Lemma lem8094549 {A B P : Type'} (_107321 : type1402 A) (_107322 : type560 A B P) (_107323 : P -> A) : (@tailadmissible A B P _107321 _107322 _107323) = (term5 A B P _107321 _107322 _107323).
Proof. exact (MK_COMB (@lem8094547 A B P _107321 _107322) (@lem8094548 A P _107323)). Qed.
Lemma lem8094550 {A B P : Type'} (_107321 : type1402 A) (_107323 : P -> A) (_107322 : type560 A B P) : (term5 A B P _107321 _107322 _107323) = (term6 A B P _107321 _107323 _107322).
Proof. exact (eq_refl (term5 A B P _107321 _107322 _107323)). Qed.
Lemma lem8094551 {A B P : Type'} (_107321 : type1402 A) (_107323 : P -> A) (_107322 : type560 A B P) : (@tailadmissible A B P _107321 _107322 _107323) = (term6 A B P _107321 _107323 _107322).
Proof. exact (TRANS (@lem8094549 A B P _107321 _107322 _107323) (@lem8094550 A B P _107321 _107323 _107322)). Qed.
Lemma lem8094552 {A B P : Type'} (_107324 : type558 A B P) : _107324 = _107324.
Proof. exact (eq_refl _107324). Qed.
Lemma lem8094553 {A B P : Type'} (_107321 : type1402 A) (_107323 : P -> A) (_107322 : type560 A B P) (_107324 : type558 A B P) : (@tailadmissible A B P _107321 _107322 _107323 _107324) = (term7 A B P _107321 _107323 _107322 _107324).
Proof. exact (MK_COMB (@lem8094551 A B P _107321 _107323 _107322) (@lem8094552 A B P _107324)). Qed.
Lemma lem8094554 {A B P : Type'} (_107321 : type1402 A) (_107323 : P -> A) (_107322 : type560 A B P) (_107324 : type558 A B P) : (term7 A B P _107321 _107323 _107322 _107324) = (term8 A B P _107321 _107323 _107322 _107324).
Proof. exact (eq_refl (term7 A B P _107321 _107323 _107322 _107324)). Qed.
Lemma lem8094555 {A B P : Type'} (_107321 : type1402 A) (_107323 : P -> A) (_107322 : type560 A B P) (_107324 : type558 A B P) : (@tailadmissible A B P _107321 _107322 _107323 _107324) = (term8 A B P _107321 _107323 _107322 _107324).
Proof. exact (TRANS (@lem8094553 A B P _107321 _107323 _107322 _107324) (@lem8094554 A B P _107321 _107323 _107322 _107324)). Qed.
Lemma lem8094556 {A B P : Type'} (_107321 : type1402 A) (_107323 : P -> A) (_107322 : type560 A B P) : term9 A B P _107321 _107323 _107322.
Proof. exact (fun _107324 : type558 A B P => @lem8094555 A B P _107321 _107323 _107322 _107324). Qed.
Lemma lem8094557 {A B P : Type'} (_107321 : type1402 A) (_107322 : type560 A B P) : term10 A B P _107321 _107322.
Proof. exact (fun _107323 : P -> A => @lem8094556 A B P _107321 _107323 _107322). Qed.
Lemma lem8094558 {A B P : Type'} (_107321 : type1402 A) : term11 A B P _107321.
Proof. exact (fun _107322 : type560 A B P => @lem8094557 A B P _107321 _107322). Qed.
Lemma lem8094559 {A B P : Type'} : term12 A B P.
Proof. exact (fun _107321 : type1402 A => @lem8094558 A B P _107321). Qed.
Lemma lem8094560 {A B P : Type'} (_107321 : type1402 A) : term13 A B P _107321.
Proof. exact (@lem8094559 A B P _107321). Qed.
Lemma lem8094561 {A B P : Type'} (_107321 : type1402 A) : (term13 A B P _107321) = (term11 A B P _107321).
Proof. exact (eq_refl (term13 A B P _107321)). Qed.
Lemma lem8094562 {A B P : Type'} (_107321 : type1402 A) : term11 A B P _107321.
Proof. exact (EQ_MP (@lem8094561 A B P _107321) (@lem8094560 A B P _107321)). Qed.
Lemma lem8094563 {A B P : Type'} (_107321 : type1402 A) (_107322 : type560 A B P) : term14 A B P _107321 _107322.
Proof. exact (@lem8094562 A B P _107321 _107322). Qed.
Lemma lem8094564 {A B P : Type'} (_107321 : type1402 A) (_107322 : type560 A B P) : (term14 A B P _107321 _107322) = (term10 A B P _107321 _107322).
Proof. exact (eq_refl (term14 A B P _107321 _107322)). Qed.
Lemma lem8094565 {A B P : Type'} (_107321 : type1402 A) (_107322 : type560 A B P) : term10 A B P _107321 _107322.
Proof. exact (EQ_MP (@lem8094564 A B P _107321 _107322) (@lem8094563 A B P _107321 _107322)). Qed.
Lemma lem8094566 {A B P : Type'} (_107321 : type1402 A) (_107322 : type560 A B P) (_107323 : P -> A) : term15 A B P _107321 _107322 _107323.
Proof. exact (@lem8094565 A B P _107321 _107322 _107323). Qed.
Lemma lem8094567 {A B P : Type'} (_107321 : type1402 A) (_107323 : P -> A) (_107322 : type560 A B P) : (term15 A B P _107321 _107322 _107323) = (term9 A B P _107321 _107323 _107322).
Proof. exact (eq_refl (term15 A B P _107321 _107322 _107323)). Qed.
Lemma lem8094568 {A B P : Type'} (_107321 : type1402 A) (_107323 : P -> A) (_107322 : type560 A B P) : term9 A B P _107321 _107323 _107322.
Proof. exact (EQ_MP (@lem8094567 A B P _107321 _107323 _107322) (@lem8094566 A B P _107321 _107322 _107323)). Qed.
Lemma lem8094569 {A B P : Type'} (_107321 : type1402 A) (_107323 : P -> A) (_107322 : type560 A B P) (_107324 : type558 A B P) : term16 A B P _107321 _107323 _107322 _107324.
Proof. exact (@lem8094568 A B P _107321 _107323 _107322 _107324). Qed.
Lemma lem8094570 {A B P : Type'} (_107321 : type1402 A) (_107323 : P -> A) (_107322 : type560 A B P) (_107324 : type558 A B P) : (term16 A B P _107321 _107323 _107322 _107324) = ((@tailadmissible A B P _107321 _107322 _107323 _107324) = (term8 A B P _107321 _107323 _107322 _107324)).
Proof. exact (eq_refl (term16 A B P _107321 _107323 _107322 _107324)). Qed.
Lemma lem8094571 {A B P : Type'} (_107321 : type1402 A) (_107323 : P -> A) (_107322 : type560 A B P) (_107324 : type558 A B P) : (@tailadmissible A B P _107321 _107322 _107323 _107324) = (term8 A B P _107321 _107323 _107322 _107324).
Proof. exact (EQ_MP (@lem8094570 A B P _107321 _107323 _107322 _107324) (@lem8094569 A B P _107321 _107323 _107322 _107324)). Qed.
Lemma lem8094640 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) : (@tailadmissible A B P lt2 p s t) = (term8 A B P lt2 s p t).
Proof. exact (@lem8094571 A B P lt2 s p t). Qed.
Lemma lem8094641 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : term9 A B P lt2 s p.
Proof. exact (fun t : type558 A B P => @lem8094640 A B P lt2 s p t). Qed.
Lemma lem8094642 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) : term17 A B P lt2 s.
Proof. exact (fun p : type560 A B P => @lem8094641 A B P lt2 s p). Qed.
Lemma lem8094643 {A B P : Type'} (lt2 : type1402 A) : term18 A B P lt2.
Proof. exact (fun s : P -> A => @lem8094642 A B P lt2 s). Qed.
Lemma lem8094644 {A B P : Type'} : term19 A B P.
Proof. exact (fun lt2 : type1402 A => @lem8094643 A B P lt2). Qed.
