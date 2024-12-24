Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1066936_term_abbrevs.
Require Import thm0_spec.
Require Import thm32_spec.
Require Import thm37_spec.
Require Import thm51_spec.
Require Import thm9103_spec.
Require Import thm9104_spec.
Require Import thm9120_spec.
Lemma lem1066573 {A B : Type'} (a : type1677 A B) (INL' : type1431 A B) (a' : A) (h1 : a = (INL' a')) : a = (INL' a').
Proof. exact (h1). Qed.
Lemma lem1066574 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (h1 : term0 A B sum' INL') : term0 A B sum' INL'.
Proof. exact (h1). Qed.
Lemma lem1066575 {A B : Type'} (a : A) (sum' : type1333 A B) (INL' : type1431 A B) (h1 : term0 A B sum' INL') : term1 A B sum' INL' a.
Proof. exact (@lem1066574 A B sum' INL' h1 a). Qed.
Lemma lem1066576 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (a : A) : (term1 A B sum' INL' a) = (term2 A B sum' INL' a).
Proof. exact (eq_refl (term1 A B sum' INL' a)). Qed.
Lemma lem1066577 {A B : Type'} (a : A) (sum' : type1333 A B) (INL' : type1431 A B) (h1 : term0 A B sum' INL') : term2 A B sum' INL' a.
Proof. exact (EQ_MP (@lem1066576 A B sum' INL' a) (@lem1066575 A B a sum' INL' h1)). Qed.
Lemma lem1066578 {A B : Type'} (sum' : type1333 A B) : sum' = sum'.
Proof. exact (eq_refl sum'). Qed.
Lemma lem1066579 {A B : Type'} (sum' : type1333 A B) (a : type1677 A B) (INL' : type1431 A B) (a' : A) (h1 : a = (INL' a')) : (sum' a) = (term2 A B sum' INL' a').
Proof. exact (MK_COMB (@lem1066578 A B sum') (@lem1066573 A B a INL' a' h1)). Qed.
Lemma lem1066580 {A B : Type'} (sum' : type1333 A B) (a : type1677 A B) (INL' : type1431 A B) (a' : A) (h1 : a = (INL' a')) : (term2 A B sum' INL' a') = (sum' a).
Proof. exact (SYM (@lem1066579 A B sum' a INL' a' h1)). Qed.
Lemma lem1066581 {A B : Type'} (sum' : type1333 A B) (a : type1677 A B) (INL' : type1431 A B) (a' : A) (h1 : term0 A B sum' INL') (h2 : a = (INL' a')) : sum' a.
Proof. exact (EQ_MP (@lem1066580 A B sum' a INL' a' h2) (@lem1066577 A B a' sum' INL' h1)). Qed.
Lemma lem1066582 {A B : Type'} (a : A) (a' : type1677 A B) (sum' : type1333 A B) (INL' : type1431 A B) (h1 : term0 A B sum' INL') : term3 A B INL' a sum' a'.
Proof. exact (fun h0 : a' = (INL' a) => @lem1066581 A B sum' a' INL' a h1 h0). Qed.
Lemma lem1066583 {A B : Type'} (a : type1677 A B) (INL' : type1431 A B) (a' : A) (h1 : a = (INL' a')) : a = (INL' a').
Proof. exact (h1). Qed.
Lemma lem1066584 {A B : Type'} (sum' : type1333 A B) (a : type1677 A B) (INL' : type1431 A B) (a' : A) (h1 : term0 A B sum' INL') (h2 : a = (INL' a')) : sum' a.
Proof. exact (@lem1066582 A B a' a sum' INL' h1 (@lem1066583 A B a INL' a' h2)). Qed.
Lemma lem1066585 {A B : Type'} (a : A) (a' : type1677 A B) (sum' : type1333 A B) (INL' : type1431 A B) (h1 : term0 A B sum' INL') : term3 A B INL' a sum' a'.
Proof. exact (fun h0 : a' = (INL' a) => @lem1066584 A B sum' a' INL' a h1 h0). Qed.
Lemma lem1066586 {A B : Type'} (a : type1677 A B) (sum' : type1333 A B) (INL' : type1431 A B) (h1 : term0 A B sum' INL') : term4 A B INL' sum' a.
Proof. exact (fun a' : A => @lem1066585 A B a' a sum' INL' h1). Qed.
Lemma lem1066587 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (h1 : term0 A B sum' INL') : term5 A B INL' sum'.
Proof. exact (fun a : type1677 A B => @lem1066586 A B a sum' INL' h1). Qed.
Lemma lem1066588 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) (h1 : term5 A B INL' sum') : term5 A B INL' sum'.
Proof. exact (h1). Qed.
Lemma lem1066589 {A B : Type'} (a : A) (INL' : type1431 A B) (sum' : type1333 A B) (h1 : term5 A B INL' sum') : term6 A B sum' INL' a.
Proof. exact (@lem1066588 A B INL' sum' h1 (INL' a)). Qed.
Lemma lem1066590 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (a : A) : (term6 A B sum' INL' a) = (term7 A B sum' INL' a).
Proof. exact (eq_refl (term6 A B sum' INL' a)). Qed.
Lemma lem1066591 {A B : Type'} (a : A) (INL' : type1431 A B) (sum' : type1333 A B) (h1 : term5 A B INL' sum') : term7 A B sum' INL' a.
Proof. exact (EQ_MP (@lem1066590 A B sum' INL' a) (@lem1066589 A B a INL' sum' h1)). Qed.
Lemma lem1066592 {A B : Type'} (a : A) (INL' : type1431 A B) (sum' : type1333 A B) (h1 : term5 A B INL' sum') : term8 A B sum' INL' a.
Proof. exact (@lem1066591 A B a INL' sum' h1 a). Qed.
Lemma lem1066593 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (a : A) : (term8 A B sum' INL' a) = (term9 A B sum' INL' a).
Proof. exact (eq_refl (term8 A B sum' INL' a)). Qed.
Lemma lem1066594 {A B : Type'} (a : A) (INL' : type1431 A B) (sum' : type1333 A B) (h1 : term5 A B INL' sum') : term9 A B sum' INL' a.
Proof. exact (EQ_MP (@lem1066593 A B sum' INL' a) (@lem1066592 A B a INL' sum' h1)). Qed.
Lemma lem1066595 {A B : Type'} (INL' : type1431 A B) (a : A) : (INL' a) = (INL' a).
Proof. exact (eq_refl (INL' a)). Qed.
Lemma lem1066596 {A B : Type'} (a : A) (INL' : type1431 A B) (sum' : type1333 A B) (h1 : term5 A B INL' sum') : term2 A B sum' INL' a.
Proof. exact (@lem1066594 A B a INL' sum' h1 (@lem1066595 A B INL' a)). Qed.
Lemma lem1066597 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) (h1 : term5 A B INL' sum') : term0 A B sum' INL'.
Proof. exact (fun a : A => @lem1066596 A B a INL' sum' h1). Qed.
Lemma lem1066598 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) : term10 A B sum' INL'.
Proof. exact (fun h0 : term5 A B INL' sum' => @lem1066597 A B INL' sum' h0). Qed.
Lemma lem1066599 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) : term11 A B INL' sum'.
Proof. exact (fun h0 : term0 A B sum' INL' => @lem1066587 A B sum' INL' h0). Qed.
Lemma lem1066600 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) : term12 A B sum' INL'.
Proof. exact (conj (@lem1066599 A B INL' sum') (@lem1066598 A B sum' INL')). Qed.
Lemma lem1066601 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) : (term12 A B sum' INL') = ((term0 A B sum' INL') = (term5 A B INL' sum')).
Proof. exact (@lem32 (term0 A B sum' INL') (term5 A B INL' sum')). Qed.
Lemma lem1066602 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) : (term0 A B sum' INL') = (term5 A B INL' sum').
Proof. exact (EQ_MP (@lem1066601 A B INL' sum') (@lem1066600 A B sum' INL')). Qed.
Lemma lem1066603 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) (a : type1677 A B) (h1 : term4 A B INL' sum' a) : term4 A B INL' sum' a.
Proof. exact (h1). Qed.
Lemma lem1066604 {A B : Type'} (a : A) (INL' : type1431 A B) (sum' : type1333 A B) (a' : type1677 A B) (h1 : term4 A B INL' sum' a') : term13 A B INL' sum' a' a.
Proof. exact (@lem1066603 A B INL' sum' a' h1 a). Qed.
Lemma lem1066605 {A B : Type'} (INL' : type1431 A B) (a : A) (sum' : type1333 A B) (a' : type1677 A B) : (term13 A B INL' sum' a' a) = (term3 A B INL' a sum' a').
Proof. exact (eq_refl (term13 A B INL' sum' a' a)). Qed.
Lemma lem1066606 {A B : Type'} (a : A) (INL' : type1431 A B) (sum' : type1333 A B) (a' : type1677 A B) (h1 : term4 A B INL' sum' a') : term3 A B INL' a sum' a'.
Proof. exact (EQ_MP (@lem1066605 A B INL' a sum' a') (@lem1066604 A B a INL' sum' a' h1)). Qed.
Lemma lem1066607 {A B : Type'} (a : type1677 A B) (INL' : type1431 A B) (a' : A) (h1 : a = (INL' a')) : a = (INL' a').
Proof. exact (h1). Qed.
Lemma lem1066608 {A B : Type'} (sum' : type1333 A B) (a : type1677 A B) (INL' : type1431 A B) (a' : A) (h1 : term4 A B INL' sum' a) (h2 : a = (INL' a')) : sum' a.
Proof. exact (@lem1066606 A B a' INL' sum' a h1 (@lem1066607 A B a INL' a' h2)). Qed.
Lemma lem1066609 {A B : Type'} (sum' : type1333 A B) (a : type1677 A B) (INL' : type1431 A B) (a' : A) (h1 : a = (INL' a')) : term14 A B INL' sum' a.
Proof. exact (fun h0 : term4 A B INL' sum' a => @lem1066608 A B sum' a INL' a' h0 h1). Qed.
Lemma lem1066610 {A B : Type'} (a : type1677 A B) (INL' : type1431 A B) (h1 : term15 A B a INL') : term15 A B a INL'.
Proof. exact (h1). Qed.
Lemma lem1066611 {A B : Type'} (sum' : type1333 A B) (a : type1677 A B) (INL' : type1431 A B) (h1 : term15 A B a INL') : term14 A B INL' sum' a.
Proof. exact (ex_elim (@lem1066610 A B a INL' h1) (fun a' : A => fun h0 : term16 A B a INL' a' => @lem1066609 A B sum' a INL' a' h0)). Qed.
Lemma lem1066612 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) (a : type1677 A B) (h1 : term4 A B INL' sum' a) : term4 A B INL' sum' a.
Proof. exact (h1). Qed.
Lemma lem1066613 {A B : Type'} (sum' : type1333 A B) (a : type1677 A B) (INL' : type1431 A B) (h1 : term4 A B INL' sum' a) (h2 : term15 A B a INL') : sum' a.
Proof. exact (@lem1066611 A B sum' a INL' h2 (@lem1066612 A B INL' sum' a h1)). Qed.
Lemma lem1066614 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) (a : type1677 A B) (h1 : term4 A B INL' sum' a) : term17 A B INL' sum' a.
Proof. exact (fun h0 : term15 A B a INL' => @lem1066613 A B sum' a INL' h1 h0). Qed.
Lemma lem1066615 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) (a : type1677 A B) (h1 : term17 A B INL' sum' a) : term17 A B INL' sum' a.
Proof. exact (h1). Qed.
Lemma lem1066616 {A B : Type'} (a : type1677 A B) (INL' : type1431 A B) (a' : A) (h1 : a = (INL' a')) : a = (INL' a').
Proof. exact (h1). Qed.
Lemma lem1066617 {A B : Type'} (a : type1677 A B) (INL' : type1431 A B) (a' : A) (h1 : a = (INL' a')) : term15 A B a INL'.
Proof. exact (ex_intro (term16 A B a INL') a' (@lem1066616 A B a INL' a' h1)). Qed.
Lemma lem1066618 {A B : Type'} (a : A) (INL' : type1431 A B) (sum' : type1333 A B) (a' : type1677 A B) (h1 : a' = (INL' a)) (h2 : term17 A B INL' sum' a') : sum' a'.
Proof. exact (@lem1066615 A B INL' sum' a' h2 (@lem1066617 A B a' INL' a h1)). Qed.
Lemma lem1066619 {A B : Type'} (a : A) (INL' : type1431 A B) (sum' : type1333 A B) (a' : type1677 A B) (h1 : term17 A B INL' sum' a') : term3 A B INL' a sum' a'.
Proof. exact (fun h0 : a' = (INL' a) => @lem1066618 A B a INL' sum' a' h0 h1). Qed.
Lemma lem1066620 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) (a : type1677 A B) (h1 : term17 A B INL' sum' a) : term4 A B INL' sum' a.
Proof. exact (fun a' : A => @lem1066619 A B a' INL' sum' a h1). Qed.
Lemma lem1066621 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) (a : type1677 A B) : term18 A B INL' sum' a.
Proof. exact (fun h0 : term17 A B INL' sum' a => @lem1066620 A B INL' sum' a h0). Qed.
Lemma lem1066622 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) (a : type1677 A B) : term19 A B INL' sum' a.
Proof. exact (fun h0 : term4 A B INL' sum' a => @lem1066614 A B INL' sum' a h0). Qed.
Lemma lem1066623 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) (a : type1677 A B) : term20 A B INL' sum' a.
Proof. exact (conj (@lem1066622 A B INL' sum' a) (@lem1066621 A B INL' sum' a)). Qed.
Lemma lem1066624 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) (a : type1677 A B) : (term20 A B INL' sum' a) = ((term4 A B INL' sum' a) = (term17 A B INL' sum' a)).
Proof. exact (@lem32 (term4 A B INL' sum' a) (term17 A B INL' sum' a)). Qed.
Lemma lem1066625 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) (a : type1677 A B) : (term4 A B INL' sum' a) = (term17 A B INL' sum' a).
Proof. exact (EQ_MP (@lem1066624 A B INL' sum' a) (@lem1066623 A B INL' sum' a)). Qed.
Lemma lem1066626 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) : (term21 A B INL' sum') = (term22 A B INL' sum').
Proof. exact (fun_ext (fun a : type1677 A B => @lem1066625 A B INL' sum' a)). Qed.
Lemma lem1066627 {A B : Type'} : (@all (recspace (prod A B))) = (@all (recspace (prod A B))).
Proof. exact (eq_refl (@all (recspace (prod A B)))). Qed.
Lemma lem1066628 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) : (term5 A B INL' sum') = (term23 A B INL' sum').
Proof. exact (MK_COMB (@lem1066627 A B) (@lem1066626 A B INL' sum')). Qed.
Lemma lem1066629 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) : (term0 A B sum' INL') = (term23 A B INL' sum').
Proof. exact (TRANS (@lem1066602 A B INL' sum') (@lem1066628 A B INL' sum')). Qed.
Lemma lem1066630 {A B : Type'} (a : type1677 A B) (INR' : type1479 A B) (a' : B) (h1 : a = (INR' a')) : a = (INR' a').
Proof. exact (h1). Qed.
Lemma lem1066631 {A B : Type'} (sum' : type1333 A B) (INR' : type1479 A B) (h1 : term24 A B sum' INR') : term24 A B sum' INR'.
Proof. exact (h1). Qed.
Lemma lem1066632 {A B : Type'} (a : B) (sum' : type1333 A B) (INR' : type1479 A B) (h1 : term24 A B sum' INR') : term25 A B sum' INR' a.
Proof. exact (@lem1066631 A B sum' INR' h1 a). Qed.
Lemma lem1066633 {A B : Type'} (sum' : type1333 A B) (INR' : type1479 A B) (a : B) : (term25 A B sum' INR' a) = (term26 A B sum' INR' a).
Proof. exact (eq_refl (term25 A B sum' INR' a)). Qed.
Lemma lem1066634 {A B : Type'} (a : B) (sum' : type1333 A B) (INR' : type1479 A B) (h1 : term24 A B sum' INR') : term26 A B sum' INR' a.
Proof. exact (EQ_MP (@lem1066633 A B sum' INR' a) (@lem1066632 A B a sum' INR' h1)). Qed.
Lemma lem1066635 {A B : Type'} (sum' : type1333 A B) : sum' = sum'.
Proof. exact (eq_refl sum'). Qed.
Lemma lem1066636 {A B : Type'} (sum' : type1333 A B) (a : type1677 A B) (INR' : type1479 A B) (a' : B) (h1 : a = (INR' a')) : (sum' a) = (term26 A B sum' INR' a').
Proof. exact (MK_COMB (@lem1066635 A B sum') (@lem1066630 A B a INR' a' h1)). Qed.
Lemma lem1066637 {A B : Type'} (sum' : type1333 A B) (a : type1677 A B) (INR' : type1479 A B) (a' : B) (h1 : a = (INR' a')) : (term26 A B sum' INR' a') = (sum' a).
Proof. exact (SYM (@lem1066636 A B sum' a INR' a' h1)). Qed.
Lemma lem1066638 {A B : Type'} (sum' : type1333 A B) (a : type1677 A B) (INR' : type1479 A B) (a' : B) (h1 : term24 A B sum' INR') (h2 : a = (INR' a')) : sum' a.
Proof. exact (EQ_MP (@lem1066637 A B sum' a INR' a' h2) (@lem1066634 A B a' sum' INR' h1)). Qed.
Lemma lem1066639 {A B : Type'} (a : B) (a' : type1677 A B) (sum' : type1333 A B) (INR' : type1479 A B) (h1 : term24 A B sum' INR') : term27 A B INR' a sum' a'.
Proof. exact (fun h0 : a' = (INR' a) => @lem1066638 A B sum' a' INR' a h1 h0). Qed.
Lemma lem1066640 {A B : Type'} (a : type1677 A B) (INR' : type1479 A B) (a' : B) (h1 : a = (INR' a')) : a = (INR' a').
Proof. exact (h1). Qed.
Lemma lem1066641 {A B : Type'} (sum' : type1333 A B) (a : type1677 A B) (INR' : type1479 A B) (a' : B) (h1 : term24 A B sum' INR') (h2 : a = (INR' a')) : sum' a.
Proof. exact (@lem1066639 A B a' a sum' INR' h1 (@lem1066640 A B a INR' a' h2)). Qed.
Lemma lem1066642 {A B : Type'} (a : B) (a' : type1677 A B) (sum' : type1333 A B) (INR' : type1479 A B) (h1 : term24 A B sum' INR') : term27 A B INR' a sum' a'.
Proof. exact (fun h0 : a' = (INR' a) => @lem1066641 A B sum' a' INR' a h1 h0). Qed.
Lemma lem1066643 {A B : Type'} (a : type1677 A B) (sum' : type1333 A B) (INR' : type1479 A B) (h1 : term24 A B sum' INR') : term28 A B INR' sum' a.
Proof. exact (fun a' : B => @lem1066642 A B a' a sum' INR' h1). Qed.
Lemma lem1066644 {A B : Type'} (sum' : type1333 A B) (INR' : type1479 A B) (h1 : term24 A B sum' INR') : term29 A B INR' sum'.
Proof. exact (fun a : type1677 A B => @lem1066643 A B a sum' INR' h1). Qed.
Lemma lem1066645 {A B : Type'} (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term29 A B INR' sum') : term29 A B INR' sum'.
Proof. exact (h1). Qed.
Lemma lem1066646 {A B : Type'} (a : B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term29 A B INR' sum') : term30 A B sum' INR' a.
Proof. exact (@lem1066645 A B INR' sum' h1 (INR' a)). Qed.
Lemma lem1066647 {A B : Type'} (sum' : type1333 A B) (INR' : type1479 A B) (a : B) : (term30 A B sum' INR' a) = (term31 A B sum' INR' a).
Proof. exact (eq_refl (term30 A B sum' INR' a)). Qed.
Lemma lem1066648 {A B : Type'} (a : B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term29 A B INR' sum') : term31 A B sum' INR' a.
Proof. exact (EQ_MP (@lem1066647 A B sum' INR' a) (@lem1066646 A B a INR' sum' h1)). Qed.
Lemma lem1066649 {A B : Type'} (a : B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term29 A B INR' sum') : term32 A B sum' INR' a.
Proof. exact (@lem1066648 A B a INR' sum' h1 a). Qed.
Lemma lem1066650 {A B : Type'} (sum' : type1333 A B) (INR' : type1479 A B) (a : B) : (term32 A B sum' INR' a) = (term33 A B sum' INR' a).
Proof. exact (eq_refl (term32 A B sum' INR' a)). Qed.
Lemma lem1066651 {A B : Type'} (a : B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term29 A B INR' sum') : term33 A B sum' INR' a.
Proof. exact (EQ_MP (@lem1066650 A B sum' INR' a) (@lem1066649 A B a INR' sum' h1)). Qed.
Lemma lem1066652 {A B : Type'} (INR' : type1479 A B) (a : B) : (INR' a) = (INR' a).
Proof. exact (eq_refl (INR' a)). Qed.
Lemma lem1066653 {A B : Type'} (a : B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term29 A B INR' sum') : term26 A B sum' INR' a.
Proof. exact (@lem1066651 A B a INR' sum' h1 (@lem1066652 A B INR' a)). Qed.
Lemma lem1066654 {A B : Type'} (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term29 A B INR' sum') : term24 A B sum' INR'.
Proof. exact (fun a : B => @lem1066653 A B a INR' sum' h1). Qed.
Lemma lem1066655 {A B : Type'} (sum' : type1333 A B) (INR' : type1479 A B) : term34 A B sum' INR'.
Proof. exact (fun h0 : term29 A B INR' sum' => @lem1066654 A B INR' sum' h0). Qed.
Lemma lem1066656 {A B : Type'} (INR' : type1479 A B) (sum' : type1333 A B) : term35 A B INR' sum'.
Proof. exact (fun h0 : term24 A B sum' INR' => @lem1066644 A B sum' INR' h0). Qed.
Lemma lem1066657 {A B : Type'} (sum' : type1333 A B) (INR' : type1479 A B) : term36 A B sum' INR'.
Proof. exact (conj (@lem1066656 A B INR' sum') (@lem1066655 A B sum' INR')). Qed.
Lemma lem1066658 {A B : Type'} (INR' : type1479 A B) (sum' : type1333 A B) : (term36 A B sum' INR') = ((term24 A B sum' INR') = (term29 A B INR' sum')).
Proof. exact (@lem32 (term24 A B sum' INR') (term29 A B INR' sum')). Qed.
Lemma lem1066659 {A B : Type'} (INR' : type1479 A B) (sum' : type1333 A B) : (term24 A B sum' INR') = (term29 A B INR' sum').
Proof. exact (EQ_MP (@lem1066658 A B INR' sum') (@lem1066657 A B sum' INR')). Qed.
Lemma lem1066660 {A B : Type'} (INR' : type1479 A B) (sum' : type1333 A B) (a : type1677 A B) (h1 : term28 A B INR' sum' a) : term28 A B INR' sum' a.
Proof. exact (h1). Qed.
Lemma lem1066661 {A B : Type'} (a : B) (INR' : type1479 A B) (sum' : type1333 A B) (a' : type1677 A B) (h1 : term28 A B INR' sum' a') : term37 A B INR' sum' a' a.
Proof. exact (@lem1066660 A B INR' sum' a' h1 a). Qed.
Lemma lem1066662 {A B : Type'} (INR' : type1479 A B) (a : B) (sum' : type1333 A B) (a' : type1677 A B) : (term37 A B INR' sum' a' a) = (term27 A B INR' a sum' a').
Proof. exact (eq_refl (term37 A B INR' sum' a' a)). Qed.
Lemma lem1066663 {A B : Type'} (a : B) (INR' : type1479 A B) (sum' : type1333 A B) (a' : type1677 A B) (h1 : term28 A B INR' sum' a') : term27 A B INR' a sum' a'.
Proof. exact (EQ_MP (@lem1066662 A B INR' a sum' a') (@lem1066661 A B a INR' sum' a' h1)). Qed.
Lemma lem1066664 {A B : Type'} (a : type1677 A B) (INR' : type1479 A B) (a' : B) (h1 : a = (INR' a')) : a = (INR' a').
Proof. exact (h1). Qed.
Lemma lem1066665 {A B : Type'} (sum' : type1333 A B) (a : type1677 A B) (INR' : type1479 A B) (a' : B) (h1 : term28 A B INR' sum' a) (h2 : a = (INR' a')) : sum' a.
Proof. exact (@lem1066663 A B a' INR' sum' a h1 (@lem1066664 A B a INR' a' h2)). Qed.
Lemma lem1066666 {A B : Type'} (sum' : type1333 A B) (a : type1677 A B) (INR' : type1479 A B) (a' : B) (h1 : a = (INR' a')) : term38 A B INR' sum' a.
Proof. exact (fun h0 : term28 A B INR' sum' a => @lem1066665 A B sum' a INR' a' h0 h1). Qed.
Lemma lem1066667 {A B : Type'} (a : type1677 A B) (INR' : type1479 A B) (h1 : term39 A B a INR') : term39 A B a INR'.
Proof. exact (h1). Qed.
Lemma lem1066668 {A B : Type'} (sum' : type1333 A B) (a : type1677 A B) (INR' : type1479 A B) (h1 : term39 A B a INR') : term38 A B INR' sum' a.
Proof. exact (ex_elim (@lem1066667 A B a INR' h1) (fun a' : B => fun h0 : term40 A B a INR' a' => @lem1066666 A B sum' a INR' a' h0)). Qed.
Lemma lem1066669 {A B : Type'} (INR' : type1479 A B) (sum' : type1333 A B) (a : type1677 A B) (h1 : term28 A B INR' sum' a) : term28 A B INR' sum' a.
Proof. exact (h1). Qed.
Lemma lem1066670 {A B : Type'} (sum' : type1333 A B) (a : type1677 A B) (INR' : type1479 A B) (h1 : term28 A B INR' sum' a) (h2 : term39 A B a INR') : sum' a.
Proof. exact (@lem1066668 A B sum' a INR' h2 (@lem1066669 A B INR' sum' a h1)). Qed.
Lemma lem1066671 {A B : Type'} (INR' : type1479 A B) (sum' : type1333 A B) (a : type1677 A B) (h1 : term28 A B INR' sum' a) : term41 A B INR' sum' a.
Proof. exact (fun h0 : term39 A B a INR' => @lem1066670 A B sum' a INR' h1 h0). Qed.
Lemma lem1066672 {A B : Type'} (INR' : type1479 A B) (sum' : type1333 A B) (a : type1677 A B) (h1 : term41 A B INR' sum' a) : term41 A B INR' sum' a.
Proof. exact (h1). Qed.
Lemma lem1066673 {A B : Type'} (a : type1677 A B) (INR' : type1479 A B) (a' : B) (h1 : a = (INR' a')) : a = (INR' a').
Proof. exact (h1). Qed.
Lemma lem1066674 {A B : Type'} (a : type1677 A B) (INR' : type1479 A B) (a' : B) (h1 : a = (INR' a')) : term39 A B a INR'.
Proof. exact (ex_intro (term40 A B a INR') a' (@lem1066673 A B a INR' a' h1)). Qed.
Lemma lem1066675 {A B : Type'} (a : B) (INR' : type1479 A B) (sum' : type1333 A B) (a' : type1677 A B) (h1 : a' = (INR' a)) (h2 : term41 A B INR' sum' a') : sum' a'.
Proof. exact (@lem1066672 A B INR' sum' a' h2 (@lem1066674 A B a' INR' a h1)). Qed.
Lemma lem1066676 {A B : Type'} (a : B) (INR' : type1479 A B) (sum' : type1333 A B) (a' : type1677 A B) (h1 : term41 A B INR' sum' a') : term27 A B INR' a sum' a'.
Proof. exact (fun h0 : a' = (INR' a) => @lem1066675 A B a INR' sum' a' h0 h1). Qed.
Lemma lem1066677 {A B : Type'} (INR' : type1479 A B) (sum' : type1333 A B) (a : type1677 A B) (h1 : term41 A B INR' sum' a) : term28 A B INR' sum' a.
Proof. exact (fun a' : B => @lem1066676 A B a' INR' sum' a h1). Qed.
Lemma lem1066678 {A B : Type'} (INR' : type1479 A B) (sum' : type1333 A B) (a : type1677 A B) : term42 A B INR' sum' a.
Proof. exact (fun h0 : term41 A B INR' sum' a => @lem1066677 A B INR' sum' a h0). Qed.
Lemma lem1066679 {A B : Type'} (INR' : type1479 A B) (sum' : type1333 A B) (a : type1677 A B) : term43 A B INR' sum' a.
Proof. exact (fun h0 : term28 A B INR' sum' a => @lem1066671 A B INR' sum' a h0). Qed.
Lemma lem1066680 {A B : Type'} (INR' : type1479 A B) (sum' : type1333 A B) (a : type1677 A B) : term44 A B INR' sum' a.
Proof. exact (conj (@lem1066679 A B INR' sum' a) (@lem1066678 A B INR' sum' a)). Qed.
Lemma lem1066681 {A B : Type'} (INR' : type1479 A B) (sum' : type1333 A B) (a : type1677 A B) : (term44 A B INR' sum' a) = ((term28 A B INR' sum' a) = (term41 A B INR' sum' a)).
Proof. exact (@lem32 (term28 A B INR' sum' a) (term41 A B INR' sum' a)). Qed.
Lemma lem1066682 {A B : Type'} (INR' : type1479 A B) (sum' : type1333 A B) (a : type1677 A B) : (term28 A B INR' sum' a) = (term41 A B INR' sum' a).
Proof. exact (EQ_MP (@lem1066681 A B INR' sum' a) (@lem1066680 A B INR' sum' a)). Qed.
Lemma lem1066683 {A B : Type'} (INR' : type1479 A B) (sum' : type1333 A B) : (term45 A B INR' sum') = (term46 A B INR' sum').
Proof. exact (fun_ext (fun a : type1677 A B => @lem1066682 A B INR' sum' a)). Qed.
Lemma lem1066684 {A B : Type'} : (@all (recspace (prod A B))) = (@all (recspace (prod A B))).
Proof. exact (eq_refl (@all (recspace (prod A B)))). Qed.
Lemma lem1066685 {A B : Type'} (INR' : type1479 A B) (sum' : type1333 A B) : (term29 A B INR' sum') = (term47 A B INR' sum').
Proof. exact (MK_COMB (@lem1066684 A B) (@lem1066683 A B INR' sum')). Qed.
Lemma lem1066686 {A B : Type'} (INR' : type1479 A B) (sum' : type1333 A B) : (term24 A B sum' INR') = (term47 A B INR' sum').
Proof. exact (TRANS (@lem1066659 A B INR' sum') (@lem1066685 A B INR' sum')). Qed.
Lemma lem1066688 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem9104 A x) (@lem9103 A x)). Qed.
Lemma lem1066689 (x : Prop) : (x = x) = True.
Proof. exact (@lem1066688 Prop x). Qed.
Lemma lem1066690 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) : ((term48 A B INL' INR' sum') = (term48 A B INL' INR' sum')) = True.
Proof. exact (@lem1066689 (term48 A B INL' INR' sum')). Qed.
Lemma lem1066691 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) : True = ((term48 A B INL' INR' sum') = (term48 A B INL' INR' sum')).
Proof. exact (SYM (@lem1066690 A B INL' INR' sum')). Qed.
Lemma lem1066692 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) : (term48 A B INL' INR' sum') = (term48 A B INL' INR' sum').
Proof. exact (EQ_MP (@lem1066691 A B INL' INR' sum') (@lem0)). Qed.
Lemma lem1066693 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1066694 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) : (term49 A B sum' INL') = (term50 A B INL' sum').
Proof. exact (MK_COMB (@lem1066693) (@lem1066629 A B INL' sum')). Qed.
Lemma lem1066695 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) : (term51 A B INL' sum' INR') = (term48 A B INL' INR' sum').
Proof. exact (MK_COMB (@lem1066694 A B INL' sum') (@lem1066686 A B INR' sum')). Qed.
Lemma lem1066696 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) : (term51 A B INL' sum' INR') = (term48 A B INL' INR' sum').
Proof. exact (TRANS (@lem1066695 A B INL' INR' sum') (@lem1066692 A B INL' INR' sum')). Qed.
Lemma lem1066697 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term48 A B INL' INR' sum') : term48 A B INL' INR' sum'.
Proof. exact (h1). Qed.
Lemma lem1066698 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term48 A B INL' INR' sum') : term47 A B INR' sum'.
Proof. exact (proj2 (@lem1066697 A B INL' INR' sum' h1)). Qed.
Lemma lem1066699 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term48 A B INL' INR' sum') : term23 A B INL' sum'.
Proof. exact (proj1 (@lem1066697 A B INL' INR' sum' h1)). Qed.
Lemma lem1066700 {A B : Type'} (a : type1677 A B) (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term48 A B INL' INR' sum') : term52 A B INL' sum' a.
Proof. exact (@lem1066699 A B INL' INR' sum' h1 a). Qed.
Lemma lem1066701 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) (a : type1677 A B) : (term52 A B INL' sum' a) = (term17 A B INL' sum' a).
Proof. exact (eq_refl (term52 A B INL' sum' a)). Qed.
Lemma lem1066702 {A B : Type'} (a : type1677 A B) (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term48 A B INL' INR' sum') : term17 A B INL' sum' a.
Proof. exact (EQ_MP (@lem1066701 A B INL' sum' a) (@lem1066700 A B a INL' INR' sum' h1)). Qed.
Lemma lem1066703 {A B : Type'} (a : type1677 A B) (INL' : type1431 A B) (h1 : term15 A B a INL') : term15 A B a INL'.
Proof. exact (h1). Qed.
Lemma lem1066704 {A B : Type'} (a : type1677 A B) (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term15 A B a INL') (h2 : term48 A B INL' INR' sum') : sum' a.
Proof. exact (@lem1066702 A B a INL' INR' sum' h2 (@lem1066703 A B a INL' h1)). Qed.
Lemma lem1066705 {A B : Type'} (INR' : type1479 A B) (sum' : type1333 A B) (a : type1677 A B) (INL' : type1431 A B) (h1 : term15 A B a INL') : term53 A B INL' INR' sum' a.
Proof. exact (fun h0 : term48 A B INL' INR' sum' => @lem1066704 A B a INL' INR' sum' h1 h0). Qed.
Lemma lem1066706 {A B : Type'} (a : type1677 A B) (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term48 A B INL' INR' sum') : term54 A B INR' sum' a.
Proof. exact (@lem1066698 A B INL' INR' sum' h1 a). Qed.
Lemma lem1066707 {A B : Type'} (INR' : type1479 A B) (sum' : type1333 A B) (a : type1677 A B) : (term54 A B INR' sum' a) = (term41 A B INR' sum' a).
Proof. exact (eq_refl (term54 A B INR' sum' a)). Qed.
Lemma lem1066708 {A B : Type'} (a : type1677 A B) (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term48 A B INL' INR' sum') : term41 A B INR' sum' a.
Proof. exact (EQ_MP (@lem1066707 A B INR' sum' a) (@lem1066706 A B a INL' INR' sum' h1)). Qed.
Lemma lem1066709 {A B : Type'} (a : type1677 A B) (INR' : type1479 A B) (h1 : term39 A B a INR') : term39 A B a INR'.
Proof. exact (h1). Qed.
Lemma lem1066710 {A B : Type'} (a : type1677 A B) (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term39 A B a INR') (h2 : term48 A B INL' INR' sum') : sum' a.
Proof. exact (@lem1066708 A B a INL' INR' sum' h2 (@lem1066709 A B a INR' h1)). Qed.
Lemma lem1066711 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) (a : type1677 A B) (INR' : type1479 A B) (h1 : term39 A B a INR') : term53 A B INL' INR' sum' a.
Proof. exact (fun h0 : term48 A B INL' INR' sum' => @lem1066710 A B a INL' INR' sum' h1 h0). Qed.
Lemma lem1066712 {A B : Type'} (INL' : type1431 A B) (a : type1677 A B) (INR' : type1479 A B) (h1 : term55 A B INL' a INR') : term55 A B INL' a INR'.
Proof. exact (h1). Qed.
Lemma lem1066713 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (a : type1677 A B) (INR' : type1479 A B) (h1 : term55 A B INL' a INR') : term53 A B INL' INR' sum' a.
Proof. exact (or_elim (@lem1066712 A B INL' a INR' h1) (fun h0 : term15 A B a INL' => @lem1066705 A B INR' sum' a INL' h0) (fun h0 : term39 A B a INR' => @lem1066711 A B INL' sum' a INR' h0)). Qed.
Lemma lem1066714 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term48 A B INL' INR' sum') : term48 A B INL' INR' sum'.
Proof. exact (h1). Qed.
Lemma lem1066715 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (a : type1677 A B) (INR' : type1479 A B) (h1 : term48 A B INL' INR' sum') (h2 : term55 A B INL' a INR') : sum' a.
Proof. exact (@lem1066713 A B sum' INL' a INR' h2 (@lem1066714 A B INL' INR' sum' h1)). Qed.
Lemma lem1066716 {A B : Type'} (a : type1677 A B) (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term48 A B INL' INR' sum') : term56 A B INL' INR' sum' a.
Proof. exact (fun h0 : term55 A B INL' a INR' => @lem1066715 A B sum' INL' a INR' h1 h0). Qed.
Lemma lem1066717 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term48 A B INL' INR' sum') : term57 A B INL' INR' sum'.
Proof. exact (fun a : type1677 A B => @lem1066716 A B a INL' INR' sum' h1). Qed.
Lemma lem1066718 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term57 A B INL' INR' sum') : term57 A B INL' INR' sum'.
Proof. exact (h1). Qed.
Lemma lem1066719 {A B : Type'} (a : type1677 A B) (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term57 A B INL' INR' sum') : term58 A B INL' INR' sum' a.
Proof. exact (@lem1066718 A B INL' INR' sum' h1 a). Qed.
Lemma lem1066720 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (a : type1677 A B) : (term58 A B INL' INR' sum' a) = (term56 A B INL' INR' sum' a).
Proof. exact (eq_refl (term58 A B INL' INR' sum' a)). Qed.
Lemma lem1066721 {A B : Type'} (a : type1677 A B) (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term57 A B INL' INR' sum') : term56 A B INL' INR' sum' a.
Proof. exact (EQ_MP (@lem1066720 A B INL' INR' sum' a) (@lem1066719 A B a INL' INR' sum' h1)). Qed.
Lemma lem1066722 {A B : Type'} (INL' : type1431 A B) (a : type1677 A B) (INR' : type1479 A B) (h1 : term55 A B INL' a INR') : term55 A B INL' a INR'.
Proof. exact (h1). Qed.
Lemma lem1066723 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (a : type1677 A B) (INR' : type1479 A B) (h1 : term57 A B INL' INR' sum') (h2 : term55 A B INL' a INR') : sum' a.
Proof. exact (@lem1066721 A B a INL' INR' sum' h1 (@lem1066722 A B INL' a INR' h2)). Qed.
Lemma lem1066724 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (a : type1677 A B) (INR' : type1479 A B) (h1 : term55 A B INL' a INR') : term59 A B INL' INR' sum' a.
Proof. exact (fun h0 : term57 A B INL' INR' sum' => @lem1066723 A B sum' INL' a INR' h0 h1). Qed.
Lemma lem1066725 {A B : Type'} (a : type1677 A B) (INR' : type1479 A B) (h1 : term39 A B a INR') : term39 A B a INR'.
Proof. exact (h1). Qed.
Lemma lem1066726 {A B : Type'} (INL' : type1431 A B) (a : type1677 A B) (INR' : type1479 A B) (h1 : term39 A B a INR') : term55 A B INL' a INR'.
Proof. exact (or_intro2 (term15 A B a INL') (@lem1066725 A B a INR' h1)). Qed.
Lemma lem1066727 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) (a : type1677 A B) (INR' : type1479 A B) (h1 : term39 A B a INR') : (term55 A B INL' a INR') = (term59 A B INL' INR' sum' a).
Proof. exact (prop_ext (fun h2 : term55 A B INL' a INR' => @lem1066724 A B sum' INL' a INR' h2) (fun h2 : term59 A B INL' INR' sum' a => @lem1066726 A B INL' a INR' h1)). Qed.
Lemma lem1066728 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) (a : type1677 A B) (INR' : type1479 A B) (h1 : term39 A B a INR') : term59 A B INL' INR' sum' a.
Proof. exact (EQ_MP (@lem1066727 A B INL' sum' a INR' h1) (@lem1066726 A B INL' a INR' h1)). Qed.
Lemma lem1066729 {A B : Type'} (a : type1677 A B) (INL' : type1431 A B) (h1 : term15 A B a INL') : term15 A B a INL'.
Proof. exact (h1). Qed.
Lemma lem1066730 {A B : Type'} (INR' : type1479 A B) (a : type1677 A B) (INL' : type1431 A B) (h1 : term15 A B a INL') : term55 A B INL' a INR'.
Proof. exact (or_intro1 (@lem1066729 A B a INL' h1) (term39 A B a INR')). Qed.
Lemma lem1066731 {A B : Type'} (INR' : type1479 A B) (sum' : type1333 A B) (a : type1677 A B) (INL' : type1431 A B) (h1 : term15 A B a INL') : (term55 A B INL' a INR') = (term59 A B INL' INR' sum' a).
Proof. exact (prop_ext (fun h2 : term55 A B INL' a INR' => @lem1066724 A B sum' INL' a INR' h2) (fun h2 : term59 A B INL' INR' sum' a => @lem1066730 A B INR' a INL' h1)). Qed.
Lemma lem1066732 {A B : Type'} (INR' : type1479 A B) (sum' : type1333 A B) (a : type1677 A B) (INL' : type1431 A B) (h1 : term15 A B a INL') : term59 A B INL' INR' sum' a.
Proof. exact (EQ_MP (@lem1066731 A B INR' sum' a INL' h1) (@lem1066730 A B INR' a INL' h1)). Qed.
Lemma lem1066733 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term57 A B INL' INR' sum') : term57 A B INL' INR' sum'.
Proof. exact (h1). Qed.
Lemma lem1066734 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) (a : type1677 A B) (INR' : type1479 A B) (h1 : term57 A B INL' INR' sum') (h2 : term39 A B a INR') : sum' a.
Proof. exact (@lem1066728 A B INL' sum' a INR' h2 (@lem1066733 A B INL' INR' sum' h1)). Qed.
Lemma lem1066735 {A B : Type'} (a : type1677 A B) (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term57 A B INL' INR' sum') : term41 A B INR' sum' a.
Proof. exact (fun h0 : term39 A B a INR' => @lem1066734 A B INL' sum' a INR' h1 h0). Qed.
Lemma lem1066736 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term57 A B INL' INR' sum') : term47 A B INR' sum'.
Proof. exact (fun a : type1677 A B => @lem1066735 A B a INL' INR' sum' h1). Qed.
Lemma lem1066737 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term57 A B INL' INR' sum') : term57 A B INL' INR' sum'.
Proof. exact (h1). Qed.
Lemma lem1066738 {A B : Type'} (INR' : type1479 A B) (sum' : type1333 A B) (a : type1677 A B) (INL' : type1431 A B) (h1 : term57 A B INL' INR' sum') (h2 : term15 A B a INL') : sum' a.
Proof. exact (@lem1066732 A B INR' sum' a INL' h2 (@lem1066737 A B INL' INR' sum' h1)). Qed.
Lemma lem1066739 {A B : Type'} (a : type1677 A B) (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term57 A B INL' INR' sum') : term17 A B INL' sum' a.
Proof. exact (fun h0 : term15 A B a INL' => @lem1066738 A B INR' sum' a INL' h1 h0). Qed.
Lemma lem1066740 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term57 A B INL' INR' sum') : term23 A B INL' sum'.
Proof. exact (fun a : type1677 A B => @lem1066739 A B a INL' INR' sum' h1). Qed.
Lemma lem1066741 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term57 A B INL' INR' sum') : term48 A B INL' INR' sum'.
Proof. exact (conj (@lem1066740 A B INL' INR' sum' h1) (@lem1066736 A B INL' INR' sum' h1)). Qed.
Lemma lem1066742 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) : term60 A B INL' INR' sum'.
Proof. exact (fun h0 : term57 A B INL' INR' sum' => @lem1066741 A B INL' INR' sum' h0). Qed.
Lemma lem1066743 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) : term61 A B INL' INR' sum'.
Proof. exact (fun h0 : term48 A B INL' INR' sum' => @lem1066717 A B INL' INR' sum' h0). Qed.
Lemma lem1066744 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) : term62 A B INL' INR' sum'.
Proof. exact (conj (@lem1066743 A B INL' INR' sum') (@lem1066742 A B INL' INR' sum')). Qed.
Lemma lem1066745 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) : (term62 A B INL' INR' sum') = ((term48 A B INL' INR' sum') = (term57 A B INL' INR' sum')).
Proof. exact (@lem32 (term48 A B INL' INR' sum') (term57 A B INL' INR' sum')). Qed.
Lemma lem1066746 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) : (term48 A B INL' INR' sum') = (term57 A B INL' INR' sum').
Proof. exact (EQ_MP (@lem1066745 A B INL' INR' sum') (@lem1066744 A B INL' INR' sum')). Qed.
Lemma lem1066747 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) : (term51 A B INL' sum' INR') = (term57 A B INL' INR' sum').
Proof. exact (TRANS (@lem1066696 A B INL' INR' sum') (@lem1066746 A B INL' INR' sum')). Qed.
Lemma lem1066748 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) (INR' : type1479 A B) : (term57 A B INL' INR' sum') = (term51 A B INL' sum' INR').
Proof. exact (SYM (@lem1066747 A B INL' INR' sum')). Qed.
Lemma lem1066749 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term63 A B INL' INR')) : sum' = (term63 A B INL' INR').
Proof. exact (h1). Qed.
Lemma lem1066750 {A B : Type'} (a : type1677 A B) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1066751 {A B : Type'} (a : type1677 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term63 A B INL' INR')) : (sum' a) = (term64 A B INL' INR' a).
Proof. exact (MK_COMB (@lem1066749 A B sum' INL' INR' h1) (@lem1066750 A B a)). Qed.
Lemma lem1066752 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (a : type1677 A B) : (term64 A B INL' INR' a) = (term65 A B INL' INR' a).
Proof. exact (eq_refl (term64 A B INL' INR' a)). Qed.
Lemma lem1066753 {A B : Type'} (sum' : type1333 A B) (a : type1677 A B) : (term66 A B sum' a) = (term66 A B sum' a).
Proof. exact (eq_refl (term66 A B sum' a)). Qed.
Lemma lem1066754 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (a : type1677 A B) : ((sum' a) = (term64 A B INL' INR' a)) = ((sum' a) = (term65 A B INL' INR' a)).
Proof. exact (MK_COMB (@lem1066753 A B sum' a) (@lem1066752 A B INL' INR' a)). Qed.
Lemma lem1066755 {A B : Type'} (a : type1677 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term63 A B INL' INR')) : (sum' a) = (term65 A B INL' INR' a).
Proof. exact (EQ_MP (@lem1066754 A B sum' INL' INR' a) (@lem1066751 A B a sum' INL' INR' h1)). Qed.
Lemma lem1066756 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term63 A B INL' INR')) : term67 A B sum' INL' INR'.
Proof. exact (fun a : type1677 A B => @lem1066755 A B a sum' INL' INR' h1). Qed.
Lemma lem1066757 {A B : Type'} (a : type1677 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term63 A B INL' INR')) : term68 A B sum' INL' INR' a.
Proof. exact (@lem1066756 A B sum' INL' INR' h1 a). Qed.
Lemma lem1066758 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (a : type1677 A B) : (term68 A B sum' INL' INR' a) = ((sum' a) = (term65 A B INL' INR' a)).
Proof. exact (eq_refl (term68 A B sum' INL' INR' a)). Qed.
Lemma lem1066759 {A B : Type'} (a : type1677 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term63 A B INL' INR')) : (sum' a) = (term65 A B INL' INR' a).
Proof. exact (EQ_MP (@lem1066758 A B sum' INL' INR' a) (@lem1066757 A B a sum' INL' INR' h1)). Qed.
Lemma lem1066762 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (a : type1677 A B) : term69 A B sum' INL' INR' a.
Proof. exact (@lem37 (sum' a) (term65 A B INL' INR' a)). Qed.
Lemma lem1066763 {A B : Type'} (a : type1677 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term63 A B INL' INR')) : term70 A B sum' INL' INR' a.
Proof. exact (@lem1066762 A B sum' INL' INR' a (@lem1066759 A B a sum' INL' INR' h1)). Qed.
Lemma lem1066764 {A B : Type'} (sum' : type1333 A B) (a : type1677 A B) (h1 : sum' a) : sum' a.
Proof. exact (h1). Qed.
Lemma lem1066765 {A B : Type'} (a : type1677 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' a) (h2 : sum' = (term63 A B INL' INR')) : term65 A B INL' INR' a.
Proof. exact (@lem1066763 A B a sum' INL' INR' h2 (@lem1066764 A B sum' a h1)). Qed.
Lemma lem1066766 {A B : Type'} (sum' : type1333 A B) (a : type1677 A B) (sum'' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum'' a) (h2 : sum'' = (term63 A B INL' INR')) : term71 A B INL' INR' a sum'.
Proof. exact (@lem1066765 A B a sum'' INL' INR' h1 h2 sum'). Qed.
Lemma lem1066767 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (a : type1677 A B) : (term71 A B INL' INR' a sum') = (term59 A B INL' INR' sum' a).
Proof. exact (eq_refl (term71 A B INL' INR' a sum')). Qed.
Lemma lem1066768 {A B : Type'} (sum' : type1333 A B) (a : type1677 A B) (sum'' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum'' a) (h2 : sum'' = (term63 A B INL' INR')) : term59 A B INL' INR' sum' a.
Proof. exact (EQ_MP (@lem1066767 A B INL' INR' sum' a) (@lem1066766 A B sum' a sum'' INL' INR' h1 h2)). Qed.
Lemma lem1066769 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term57 A B INL' INR' sum') : term57 A B INL' INR' sum'.
Proof. exact (h1). Qed.
Lemma lem1066770 {A B : Type'} (sum' : type1333 A B) (a : type1677 A B) (sum'' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term57 A B INL' INR' sum') (h2 : sum'' a) (h3 : sum'' = (term63 A B INL' INR')) : sum' a.
Proof. exact (@lem1066768 A B sum' a sum'' INL' INR' h2 h3 (@lem1066769 A B INL' INR' sum' h1)). Qed.
Lemma lem1066771 {A B : Type'} (a : type1677 A B) (sum' : type1333 A B) (sum'' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term57 A B INL' INR' sum') (h2 : sum'' = (term63 A B INL' INR')) : term72 A B sum'' sum' a.
Proof. exact (fun h0 : sum'' a => @lem1066770 A B sum' a sum'' INL' INR' h1 h0 h2). Qed.
Lemma lem1066772 {A B : Type'} (sum' : type1333 A B) (sum'' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term57 A B INL' INR' sum') (h2 : sum'' = (term63 A B INL' INR')) : term73 A B sum'' sum'.
Proof. exact (fun a : type1677 A B => @lem1066771 A B a sum' sum'' INL' INR' h1 h2). Qed.
Lemma lem1066773 {A B : Type'} (sum' : type1333 A B) (sum'' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum'' = (term63 A B INL' INR')) : term74 A B INL' INR' sum'' sum'.
Proof. exact (fun h0 : term57 A B INL' INR' sum' => @lem1066772 A B sum' sum'' INL' INR' h0 h1). Qed.
Lemma lem1066774 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term63 A B INL' INR')) : term75 A B INL' INR' sum'.
Proof. exact (fun sum'' : type1333 A B => @lem1066773 A B sum'' sum' INL' INR' h1). Qed.
Lemma lem1066775 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') : term76 A B INL' INR'.
Proof. exact (h1). Qed.
Lemma lem1066776 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term57 A B INL' INR' sum') : term57 A B INL' INR' sum'.
Proof. exact (h1). Qed.
Lemma lem1066777 {A B : Type'} (sum' : type1333 A B) (sum'' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum'' = (term63 A B INL' INR')) : term77 A B INL' INR' sum'' sum'.
Proof. exact (@lem1066774 A B sum'' INL' INR' h1 sum'). Qed.
Lemma lem1066778 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (sum'' : type1333 A B) : (term77 A B INL' INR' sum' sum'') = (term74 A B INL' INR' sum' sum'').
Proof. exact (eq_refl (term77 A B INL' INR' sum' sum'')). Qed.
Lemma lem1066779 {A B : Type'} (sum' : type1333 A B) (sum'' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum'' = (term63 A B INL' INR')) : term74 A B INL' INR' sum'' sum'.
Proof. exact (EQ_MP (@lem1066778 A B INL' INR' sum'' sum') (@lem1066777 A B sum' sum'' INL' INR' h1)). Qed.
Lemma lem1066780 {A B : Type'} (sum' : type1333 A B) (sum'' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term57 A B INL' INR' sum') (h2 : sum'' = (term63 A B INL' INR')) : term73 A B sum'' sum'.
Proof. exact (@lem1066779 A B sum' sum'' INL' INR' h2 (@lem1066776 A B INL' INR' sum' h1)). Qed.
Lemma lem1066781 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') : term78 A B INL' INR' sum'.
Proof. exact (@lem1066775 A B INL' INR' h1 sum'). Qed.
Lemma lem1066782 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) : (term78 A B INL' INR' sum') = (term79 A B sum' INL' INR').
Proof. exact (eq_refl (term78 A B INL' INR' sum')). Qed.
Lemma lem1066783 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') : term79 A B sum' INL' INR'.
Proof. exact (EQ_MP (@lem1066782 A B sum' INL' INR') (@lem1066781 A B sum' INL' INR' h1)). Qed.
Lemma lem1066784 {A B : Type'} (sum' : type1333 A B) (sum'' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') : term80 A B sum' INL' INR' sum''.
Proof. exact (@lem1066783 A B sum' INL' INR' h1 sum''). Qed.
Lemma lem1066785 {A B : Type'} (sum' : type1333 A B) (sum'' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) : (term80 A B sum' INL' INR' sum'') = (term81 A B sum' sum'' INL' INR').
Proof. exact (eq_refl (term80 A B sum' INL' INR' sum'')). Qed.
Lemma lem1066786 {A B : Type'} (sum' : type1333 A B) (sum'' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') : term81 A B sum' sum'' INL' INR'.
Proof. exact (EQ_MP (@lem1066785 A B sum' sum'' INL' INR') (@lem1066784 A B sum' sum'' INL' INR' h1)). Qed.
Lemma lem1066787 {A B : Type'} (sum' : type1333 A B) (sum'' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : term57 A B INL' INR' sum') (h3 : sum'' = (term63 A B INL' INR')) : term82 A B INL' INR'.
Proof. exact (@lem1066786 A B sum'' sum' INL' INR' h1 (@lem1066780 A B sum' sum'' INL' INR' h2 h3)). Qed.
Lemma lem1066788 {A B : Type'} (a : type1677 A B) (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term57 A B INL' INR' sum') : term58 A B INL' INR' sum' a.
Proof. exact (@lem1066776 A B INL' INR' sum' h1 a). Qed.
Lemma lem1066789 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (a : type1677 A B) : (term58 A B INL' INR' sum' a) = (term56 A B INL' INR' sum' a).
Proof. exact (eq_refl (term58 A B INL' INR' sum' a)). Qed.
Lemma lem1066790 {A B : Type'} (a : type1677 A B) (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (h1 : term57 A B INL' INR' sum') : term56 A B INL' INR' sum' a.
Proof. exact (EQ_MP (@lem1066789 A B INL' INR' sum' a) (@lem1066788 A B a INL' INR' sum' h1)). Qed.
Lemma lem1066791 {A B : Type'} (a : type1677 A B) (sum' : type1333 A B) (sum'' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : term57 A B INL' INR' sum') (h3 : sum'' = (term63 A B INL' INR')) : term83 A B INL' INR' a.
Proof. exact (@lem1066787 A B sum' sum'' INL' INR' h1 h2 h3 a). Qed.
Lemma lem1066792 {A B : Type'} (INL' : type1431 A B) (a : type1677 A B) (INR' : type1479 A B) : (term83 A B INL' INR' a) = (term84 A B INL' a INR').
Proof. exact (eq_refl (term83 A B INL' INR' a)). Qed.
Lemma lem1066793 {A B : Type'} (a : type1677 A B) (sum' : type1333 A B) (sum'' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : term57 A B INL' INR' sum') (h3 : sum'' = (term63 A B INL' INR')) : term84 A B INL' a INR'.
Proof. exact (EQ_MP (@lem1066792 A B INL' a INR') (@lem1066791 A B a sum' sum'' INL' INR' h1 h2 h3)). Qed.
Lemma lem1066794 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (a : type1677 A B) : term85 A B INL' INR' sum' a.
Proof. exact (@lem51 (term55 A B INL' a INR') (term55 A B INL' a INR') (sum' a)). Qed.
Lemma lem1066795 {A B : Type'} (a : type1677 A B) (sum' : type1333 A B) (sum'' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : term57 A B INL' INR' sum') (h3 : sum'' = (term63 A B INL' INR')) : term86 A B INL' INR' sum' a.
Proof. exact (@lem1066794 A B INL' INR' sum' a (@lem1066793 A B a sum' sum'' INL' INR' h1 h2 h3)). Qed.
Lemma lem1066796 {A B : Type'} (a : type1677 A B) (sum' : type1333 A B) (sum'' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : term57 A B INL' INR' sum') (h3 : sum'' = (term63 A B INL' INR')) : term56 A B INL' INR' sum' a.
Proof. exact (@lem1066795 A B a sum' sum'' INL' INR' h1 h2 h3 (@lem1066790 A B a INL' INR' sum' h2)). Qed.
Lemma lem1066797 {A B : Type'} (INL' : type1431 A B) (a : type1677 A B) (INR' : type1479 A B) (h1 : term55 A B INL' a INR') : term55 A B INL' a INR'.
Proof. exact (h1). Qed.
Lemma lem1066798 {A B : Type'} (sum' : type1333 A B) (sum'' : type1333 A B) (INL' : type1431 A B) (a : type1677 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : term57 A B INL' INR' sum') (h3 : sum'' = (term63 A B INL' INR')) (h4 : term55 A B INL' a INR') : sum' a.
Proof. exact (@lem1066796 A B a sum' sum'' INL' INR' h1 h2 h3 (@lem1066797 A B INL' a INR' h4)). Qed.
Lemma lem1066799 {A B : Type'} (sum' : type1333 A B) (sum'' : type1333 A B) (INL' : type1431 A B) (a : type1677 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : sum'' = (term63 A B INL' INR')) (h3 : term55 A B INL' a INR') : term59 A B INL' INR' sum' a.
Proof. exact (fun h0 : term57 A B INL' INR' sum' => @lem1066798 A B sum' sum'' INL' a INR' h1 h0 h2 h3). Qed.
Lemma lem1066800 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (a : type1677 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : sum' = (term63 A B INL' INR')) (h3 : term55 A B INL' a INR') : term65 A B INL' INR' a.
Proof. exact (fun sum'' : type1333 A B => @lem1066799 A B sum'' sum' INL' a INR' h1 h2 h3). Qed.
Lemma lem1066801 {A B : Type'} (a : type1677 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term63 A B INL' INR')) : term68 A B sum' INL' INR' a.
Proof. exact (@lem1066756 A B sum' INL' INR' h1 a). Qed.
Lemma lem1066802 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (a : type1677 A B) : (term68 A B sum' INL' INR' a) = ((sum' a) = (term65 A B INL' INR' a)).
Proof. exact (eq_refl (term68 A B sum' INL' INR' a)). Qed.
Lemma lem1066803 {A B : Type'} (a : type1677 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term63 A B INL' INR')) : (sum' a) = (term65 A B INL' INR' a).
Proof. exact (EQ_MP (@lem1066802 A B sum' INL' INR' a) (@lem1066801 A B a sum' INL' INR' h1)). Qed.
Lemma lem1066804 {A B : Type'} (a : type1677 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term63 A B INL' INR')) : (term65 A B INL' INR' a) = (sum' a).
Proof. exact (SYM (@lem1066803 A B a sum' INL' INR' h1)). Qed.
Lemma lem1066805 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (a : type1677 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : sum' = (term63 A B INL' INR')) (h3 : term55 A B INL' a INR') : sum' a.
Proof. exact (EQ_MP (@lem1066804 A B a sum' INL' INR' h2) (@lem1066800 A B sum' INL' a INR' h1 h2 h3)). Qed.
Lemma lem1066806 {A B : Type'} (a : type1677 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : sum' = (term63 A B INL' INR')) : term56 A B INL' INR' sum' a.
Proof. exact (fun h0 : term55 A B INL' a INR' => @lem1066805 A B sum' INL' a INR' h1 h2 h0). Qed.
Lemma lem1066807 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : sum' = (term63 A B INL' INR')) : term57 A B INL' INR' sum'.
Proof. exact (fun a : type1677 A B => @lem1066806 A B a sum' INL' INR' h1 h2). Qed.
Lemma lem1066810 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (a : type1677 A B) : (term87 A B INL' INR' a) = (term87 A B INL' INR' a).
Proof. exact (eq_refl (term87 A B INL' INR' a)). Qed.
Lemma lem1066811 {A B : Type'} (INL' : type1431 A B) (a : type1677 A B) (INR' : type1479 A B) : (term87 A B INL' INR' a) = (term55 A B INL' a INR').
Proof. exact (eq_refl (term87 A B INL' INR' a)). Qed.
Lemma lem1066812 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (a : type1677 A B) : (term88 A B INL' INR' a) = (term88 A B INL' INR' a).
Proof. exact (eq_refl (term88 A B INL' INR' a)). Qed.
Lemma lem1066813 {A B : Type'} (INL' : type1431 A B) (a : type1677 A B) (INR' : type1479 A B) : ((term87 A B INL' INR' a) = (term87 A B INL' INR' a)) = ((term87 A B INL' INR' a) = (term55 A B INL' a INR')).
Proof. exact (MK_COMB (@lem1066812 A B INL' INR' a) (@lem1066811 A B INL' a INR')). Qed.
Lemma lem1066814 {A B : Type'} (INL' : type1431 A B) (a : type1677 A B) (INR' : type1479 A B) : (term87 A B INL' INR' a) = (term55 A B INL' a INR').
Proof. exact (EQ_MP (@lem1066813 A B INL' a INR') (@lem1066810 A B INL' INR' a)). Qed.
Lemma lem1066815 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1066816 {A B : Type'} (INL' : type1431 A B) (a : type1677 A B) (INR' : type1479 A B) : (term89 A B INL' INR' a) = (term90 A B INL' a INR').
Proof. exact (MK_COMB (@lem1066815) (@lem1066814 A B INL' a INR')). Qed.
Lemma lem1066817 {A B : Type'} (sum' : type1333 A B) (a : type1677 A B) : (sum' a) = (sum' a).
Proof. exact (eq_refl (sum' a)). Qed.
Lemma lem1066818 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (a : type1677 A B) : (term91 A B INL' INR' sum' a) = (term56 A B INL' INR' sum' a).
Proof. exact (MK_COMB (@lem1066816 A B INL' a INR') (@lem1066817 A B sum' a)). Qed.
Lemma lem1066819 {A B : Type'} (INL' : type1431 A B) (a : type1677 A B) (INR' : type1479 A B) : (term90 A B INL' a INR') = (term90 A B INL' a INR').
Proof. exact (eq_refl (term90 A B INL' a INR')). Qed.
Lemma lem1066820 {A B : Type'} (INL' : type1431 A B) (a : type1677 A B) (INR' : type1479 A B) : (term92 A B INL' INR' a) = (term84 A B INL' a INR').
Proof. exact (MK_COMB (@lem1066819 A B INL' a INR') (@lem1066814 A B INL' a INR')). Qed.
Lemma lem1066821 {A B : Type'} (sum' : type1333 A B) (a : type1677 A B) : (term93 A B sum' a) = (term93 A B sum' a).
Proof. exact (eq_refl (term93 A B sum' a)). Qed.
Lemma lem1066822 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (a : type1677 A B) (INR' : type1479 A B) : (term94 A B sum' INL' INR' a) = (term95 A B sum' INL' a INR').
Proof. exact (MK_COMB (@lem1066821 A B sum' a) (@lem1066814 A B INL' a INR')). Qed.
Lemma lem1066823 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) : (term96 A B sum' INL' INR') = (term97 A B sum' INL' INR').
Proof. exact (fun_ext (fun a : type1677 A B => @lem1066822 A B sum' INL' a INR')). Qed.
Lemma lem1066824 {A B : Type'} : (@all (recspace (prod A B))) = (@all (recspace (prod A B))).
Proof. exact (eq_refl (@all (recspace (prod A B)))). Qed.
Lemma lem1066825 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) : (term98 A B sum' INL' INR') = (term99 A B sum' INL' INR').
Proof. exact (MK_COMB (@lem1066824 A B) (@lem1066823 A B sum' INL' INR')). Qed.
Lemma lem1066826 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) : (term100 A B INL' INR') = (term101 A B INL' INR').
Proof. exact (fun_ext (fun a : type1677 A B => @lem1066820 A B INL' a INR')). Qed.
Lemma lem1066827 {A B : Type'} : (@all (recspace (prod A B))) = (@all (recspace (prod A B))).
Proof. exact (eq_refl (@all (recspace (prod A B)))). Qed.
Lemma lem1066828 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) : (term102 A B INL' INR') = (term82 A B INL' INR').
Proof. exact (MK_COMB (@lem1066827 A B) (@lem1066826 A B INL' INR')). Qed.
Lemma lem1066829 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) : (term103 A B INL' INR' sum') = (term104 A B INL' INR' sum').
Proof. exact (fun_ext (fun a : type1677 A B => @lem1066818 A B INL' INR' sum' a)). Qed.
Lemma lem1066830 {A B : Type'} : (@all (recspace (prod A B))) = (@all (recspace (prod A B))).
Proof. exact (eq_refl (@all (recspace (prod A B)))). Qed.
Lemma lem1066831 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) : (term105 A B INL' INR' sum') = (term57 A B INL' INR' sum').
Proof. exact (MK_COMB (@lem1066830 A B) (@lem1066829 A B INL' INR' sum')). Qed.
Lemma lem1066832 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) : (term57 A B INL' INR' sum') = (term105 A B INL' INR' sum').
Proof. exact (SYM (@lem1066831 A B INL' INR' sum')). Qed.
Lemma lem1066833 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : sum' = (term63 A B INL' INR')) : term105 A B INL' INR' sum'.
Proof. exact (EQ_MP (@lem1066832 A B INL' INR' sum') (@lem1066807 A B sum' INL' INR' h1 h2)). Qed.
Lemma lem1066834 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') : term106 A B INL' INR'.
Proof. exact (@lem1066775 A B INL' INR' h1 (term107 A B INL' INR')). Qed.
Lemma lem1066835 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) : (term106 A B INL' INR') = (term108 A B INL' INR').
Proof. exact (eq_refl (term106 A B INL' INR')). Qed.
Lemma lem1066836 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') : term108 A B INL' INR'.
Proof. exact (EQ_MP (@lem1066835 A B INL' INR') (@lem1066834 A B INL' INR' h1)). Qed.
Lemma lem1066837 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') : term109 A B INL' INR' sum'.
Proof. exact (@lem1066836 A B INL' INR' h1 sum'). Qed.
Lemma lem1066838 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) : (term109 A B INL' INR' sum') = (term110 A B sum' INL' INR').
Proof. exact (eq_refl (term109 A B INL' INR' sum')). Qed.
Lemma lem1066839 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') : term110 A B sum' INL' INR'.
Proof. exact (EQ_MP (@lem1066838 A B sum' INL' INR') (@lem1066837 A B sum' INL' INR' h1)). Qed.
Lemma lem1066840 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : sum' = (term63 A B INL' INR')) : term82 A B INL' INR'.
Proof. exact (@lem1066839 A B sum' INL' INR' h1 (@lem1066833 A B sum' INL' INR' h1 h2)). Qed.
Lemma lem1066841 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) : (term82 A B INL' INR') = (term102 A B INL' INR').
Proof. exact (SYM (@lem1066828 A B INL' INR')). Qed.
Lemma lem1066842 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : sum' = (term63 A B INL' INR')) : term102 A B INL' INR'.
Proof. exact (EQ_MP (@lem1066841 A B INL' INR') (@lem1066840 A B sum' INL' INR' h1 h2)). Qed.
Lemma lem1066843 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term63 A B INL' INR')) : term111 A B sum' INL' INR'.
Proof. exact (@lem1066774 A B sum' INL' INR' h1 (term107 A B INL' INR')). Qed.
Lemma lem1066844 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) : (term111 A B sum' INL' INR') = (term112 A B sum' INL' INR').
Proof. exact (eq_refl (term111 A B sum' INL' INR')). Qed.
Lemma lem1066845 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term63 A B INL' INR')) : term112 A B sum' INL' INR'.
Proof. exact (EQ_MP (@lem1066844 A B sum' INL' INR') (@lem1066843 A B sum' INL' INR' h1)). Qed.
Lemma lem1066846 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : sum' = (term63 A B INL' INR')) : term98 A B sum' INL' INR'.
Proof. exact (@lem1066845 A B sum' INL' INR' h2 (@lem1066842 A B sum' INL' INR' h1 h2)). Qed.
Lemma lem1066847 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : sum' = (term63 A B INL' INR')) : term99 A B sum' INL' INR'.
Proof. exact (EQ_MP (@lem1066825 A B sum' INL' INR') (@lem1066846 A B sum' INL' INR' h1 h2)). Qed.
Lemma lem1066848 {A B : Type'} (a : type1677 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : sum' = (term63 A B INL' INR')) : term58 A B INL' INR' sum' a.
Proof. exact (@lem1066807 A B sum' INL' INR' h1 h2 a). Qed.
Lemma lem1066849 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (a : type1677 A B) : (term58 A B INL' INR' sum' a) = (term56 A B INL' INR' sum' a).
Proof. exact (eq_refl (term58 A B INL' INR' sum' a)). Qed.
Lemma lem1066850 {A B : Type'} (a : type1677 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : sum' = (term63 A B INL' INR')) : term56 A B INL' INR' sum' a.
Proof. exact (EQ_MP (@lem1066849 A B INL' INR' sum' a) (@lem1066848 A B a sum' INL' INR' h1 h2)). Qed.
Lemma lem1066851 {A B : Type'} (a : type1677 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : sum' = (term63 A B INL' INR')) : term113 A B sum' INL' INR' a.
Proof. exact (@lem1066847 A B sum' INL' INR' h1 h2 a). Qed.
Lemma lem1066852 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (a : type1677 A B) (INR' : type1479 A B) : (term113 A B sum' INL' INR' a) = (term95 A B sum' INL' a INR').
Proof. exact (eq_refl (term113 A B sum' INL' INR' a)). Qed.
Lemma lem1066853 {A B : Type'} (a : type1677 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : sum' = (term63 A B INL' INR')) : term95 A B sum' INL' a INR'.
Proof. exact (EQ_MP (@lem1066852 A B sum' INL' a INR') (@lem1066851 A B a sum' INL' INR' h1 h2)). Qed.
Lemma lem1066854 {A B : Type'} (a : type1677 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : sum' = (term63 A B INL' INR')) : term114 A B INL' INR' sum' a.
Proof. exact (conj (@lem1066853 A B a sum' INL' INR' h1 h2) (@lem1066850 A B a sum' INL' INR' h1 h2)). Qed.
Lemma lem1066855 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (a : type1677 A B) (INR' : type1479 A B) : (term114 A B INL' INR' sum' a) = ((sum' a) = (term55 A B INL' a INR')).
Proof. exact (@lem32 (sum' a) (term55 A B INL' a INR')). Qed.
Lemma lem1066856 {A B : Type'} (a : type1677 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : sum' = (term63 A B INL' INR')) : (sum' a) = (term55 A B INL' a INR').
Proof. exact (EQ_MP (@lem1066855 A B sum' INL' a INR') (@lem1066854 A B a sum' INL' INR' h1 h2)). Qed.
Lemma lem1066861 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : sum' = (term63 A B INL' INR')) : term57 A B INL' INR' sum'.
Proof. exact (fun a : type1677 A B => @lem1066806 A B a sum' INL' INR' h1 h2). Qed.
Lemma lem1066862 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : sum' = (term63 A B INL' INR')) : term115 A B sum' INL' INR'.
Proof. exact (fun a : type1677 A B => @lem1066856 A B a sum' INL' INR' h1 h2). Qed.
Lemma lem1066863 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : sum' = (term63 A B INL' INR')) : term75 A B INL' INR' sum'.
Proof. exact (fun sum'' : type1333 A B => @lem1066773 A B sum'' sum' INL' INR' h2). Qed.
Lemma lem1066864 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : sum' = (term63 A B INL' INR')) : term51 A B INL' sum' INR'.
Proof. exact (EQ_MP (@lem1066748 A B INL' sum' INR') (@lem1066861 A B sum' INL' INR' h1 h2)). Qed.
Lemma lem1066878 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) (INR' : type1479 A B) : (term57 A B INL' INR' sum') = (term51 A B INL' sum' INR').
Proof. exact (SYM (@lem1066747 A B INL' INR' sum')). Qed.
Lemma lem1066879 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) (INR' : type1479 A B) : (term57 A B INL' INR' sum') = (term51 A B INL' sum' INR').
Proof. exact (@lem1066878 A B INL' sum' INR'). Qed.
Lemma lem1066880 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) (INR' : type1479 A B) : (term57 A B INL' INR' sum') = (term51 A B INL' sum' INR').
Proof. exact (@lem1066879 A B INL' sum' INR'). Qed.
Lemma lem1066881 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1066882 {A B : Type'} (INL' : type1431 A B) (sum' : type1333 A B) (INR' : type1479 A B) : (term116 A B INL' INR' sum') = (term117 A B INL' sum' INR').
Proof. exact (MK_COMB (@lem1066881) (@lem1066880 A B INL' sum' INR')). Qed.
Lemma lem1066907 {A B : Type'} (sum' : type1333 A B) (sum'' : type1333 A B) : (term73 A B sum' sum'') = (term73 A B sum' sum'').
Proof. exact (eq_refl (term73 A B sum' sum'')). Qed.
Lemma lem1066908 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (sum'' : type1333 A B) : (term74 A B INL' INR' sum' sum'') = (term118 A B INL' INR' sum' sum'').
Proof. exact (MK_COMB (@lem1066882 A B INL' sum'' INR') (@lem1066907 A B sum' sum'')). Qed.
Lemma lem1066909 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) : (term119 A B INL' INR' sum') = (term120 A B INL' INR' sum').
Proof. exact (fun_ext (fun sum'' : type1333 A B => @lem1066908 A B INL' INR' sum' sum'')). Qed.
Lemma lem1066910 {A B : Type'} : (@all ((recspace (prod A B)) -> Prop)) = (@all ((recspace (prod A B)) -> Prop)).
Proof. exact (eq_refl (@all ((recspace (prod A B)) -> Prop))). Qed.
Lemma lem1066911 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) : (term75 A B INL' INR' sum') = (term121 A B INL' INR' sum').
Proof. exact (MK_COMB (@lem1066910 A B) (@lem1066909 A B INL' INR' sum')). Qed.
Lemma lem1066912 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : sum' = (term63 A B INL' INR')) : term121 A B INL' INR' sum'.
Proof. exact (EQ_MP (@lem1066911 A B INL' INR' sum') (@lem1066863 A B sum' INL' INR' h1 h2)). Qed.
Lemma lem1066913 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : sum' = (term63 A B INL' INR')) : term122 A B sum' INL' INR'.
Proof. exact (conj (@lem1066912 A B sum' INL' INR' h1 h2) (@lem1066862 A B sum' INL' INR' h1 h2)). Qed.
Lemma lem1066914 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term76 A B INL' INR') (h2 : sum' = (term63 A B INL' INR')) : term123 A B sum' INL' INR'.
Proof. exact (conj (@lem1066864 A B sum' INL' INR' h1 h2) (@lem1066913 A B sum' INL' INR' h1 h2)). Qed.
Lemma lem1066916 {A B : Type'} (INL' : type1431 A B) (a : type1677 A B) (INR' : type1479 A B) : term124 A B INL' a INR'.
Proof. exact (@lem9120 (term55 A B INL' a INR')). Qed.
Lemma lem1066917 {A B : Type'} (INL' : type1431 A B) (a : type1677 A B) (INR' : type1479 A B) : (term124 A B INL' a INR') = (term84 A B INL' a INR').
Proof. exact (eq_refl (term124 A B INL' a INR')). Qed.
Lemma lem1066918 {A B : Type'} (INL' : type1431 A B) (a : type1677 A B) (INR' : type1479 A B) : term84 A B INL' a INR'.
Proof. exact (EQ_MP (@lem1066917 A B INL' a INR') (@lem1066916 A B INL' a INR')). Qed.
Lemma lem1066923 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) : term82 A B INL' INR'.
Proof. exact (fun a : type1677 A B => @lem1066918 A B INL' a INR'). Qed.
Lemma lem1066924 {A B : Type'} (sum' : type1333 A B) (sum'' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) : term81 A B sum' sum'' INL' INR'.
Proof. exact (fun h0 : term73 A B sum' sum'' => @lem1066923 A B INL' INR'). Qed.
Lemma lem1066929 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) : term79 A B sum' INL' INR'.
Proof. exact (fun sum'' : type1333 A B => @lem1066924 A B sum' sum'' INL' INR'). Qed.
Lemma lem1066934 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) : term76 A B INL' INR'.
Proof. exact (fun sum' : type1333 A B => @lem1066929 A B sum' INL' INR'). Qed.
Lemma lem1066935 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term63 A B INL' INR')) : (term76 A B INL' INR') = (term123 A B sum' INL' INR').
Proof. exact (prop_ext (fun h2 : term76 A B INL' INR' => @lem1066914 A B sum' INL' INR' h2 h1) (fun h2 : term123 A B sum' INL' INR' => @lem1066934 A B INL' INR')). Qed.
Lemma lem1066936 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term63 A B INL' INR')) : term123 A B sum' INL' INR'.
Proof. exact (EQ_MP (@lem1066935 A B sum' INL' INR' h1) (@lem1066934 A B INL' INR')). Qed.
